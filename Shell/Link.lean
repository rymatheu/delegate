import Leanfc
import Std.Async.UDP

/-!
# Shell.Link (the MAVLink UDP link: IO only)

One UDP socket, bound to `bindHost:bindPort` (port 0: any free port), sending to the ground
station at `host:port` (QGroundControl listens on 14550 and answers the sender's address). A
receiver thread puts every datagram into a queue; `take` hands the queued bytes to the pure parser
(`Parser.feedBytes`) without blocking, and the frames become `Incoming` messages for the services.
`send` frames the outgoing messages as MAVLink 2 with a running sequence number. An optional log
records every frame received and sent (time in s of simulated time, direction, system, component,
message name, payload hex), which `sim/mavlink/run_qgc.py` decodes.

Also here: the cosine of the origin latitude, computed once with `Float.cos` and rounded to
binary32 (the pure code takes it as data and never computes a cosine).
-/

open Mavlink Std.Net

def hexDigit (n : Nat) : Char := "0123456789abcdef".toList.getD n '0'

def toHex (b : ByteArray) : String :=
  String.ofList (b.data.toList.flatMap fun x => [hexDigit (x.toNat / 16), hexDigit (x.toNat % 16)])

/-- The origin with its cosine of latitude (the one transcendental of the whole system, at setup). -/
def makeOrigin (latE7 lonE7 altMm : Int) : Origin :=
  let lat := Float.ofInt latE7 / 10000000.0
  { latE7, lonE7, altMm, cosLat := R.ofFloat (Float.cos (lat * 3.141592653589793 / 180.0)) }

def frameName (f : Frame) : String := match f.msg? with | some m => m.name | none => s!"#{f.msgid}"

structure Link where
  sock : Std.Async.UDP.Socket
  dst : SocketAddress
  inbox : IO.Ref (Array ByteArray)
  stop : IO.Ref Bool
  parser : IO.Ref ParserState
  queue : IO.Ref (Array Incoming)
  seq : IO.Ref UInt8
  log : Option IO.FS.Handle
  sysid : UInt8
  compid : UInt8

namespace Link

/-- Open the socket and start the receiver thread; the local port on success. -/
def open_ (host : String) (port : Nat) (bindHost : String) (bindPort : Nat) (logFile : Option String)
    (sysid compid : UInt8) : IO (Except String (Link × UInt16)) := do
  let some dst := IPv4Addr.ofString host | return .error s!"--host {host}: not an IPv4 address"
  let some src := IPv4Addr.ofString bindHost | return .error s!"--bind-host {bindHost}: not an IPv4 address"
  let sock ← Std.Async.UDP.Socket.mk
  sock.bind (.v4 { addr := src, port := bindPort.toUInt16 })
  let localPort := match ← sock.getSockName with | .v4 a => a.port | .v6 a => a.port
  let log ← match logFile with
    | some f => some <$> IO.FS.Handle.mk f .write
    | none => pure none
  let inbox ← IO.mkRef (#[] : Array ByteArray)
  let stop ← IO.mkRef false
  let _ ← IO.asTask (prio := .dedicated) do
    repeat
      if ← stop.get then break
      try
        let (data, _) ← (sock.recv 65536).block
        inbox.modify (·.push data)
      catch _ => IO.sleep 1
  let l : Link :=
    { sock, dst := .v4 { addr := dst, port := port.toUInt16 }, inbox, stop, parser := ← IO.mkRef {},
      queue := ← IO.mkRef #[], seq := ← IO.mkRef 0, log, sysid, compid }
  return .ok (l, localPort)

def logLine (l : Link) (s : String) : IO Unit := do
  if let some h := l.log then h.putStrLn s

/-- The datagrams received so far through the parser into the queue, then the first queued
message (at most one per tick; the rest wait). Never blocks. -/
def take (l : Link) (tSec : Float) : IO (Option Incoming) := do
  let datas ← l.inbox.modifyGet fun q => (q, #[])
  for d in datas do
    let (p, fs) := Parser.feedBytes (← l.parser.get) d
    l.parser.set p
    for f in fs do
      l.logLine s!"{tSec} RX {f.sysid} {f.compid} {frameName f} {toHex f.payload}"
      if let some m := f.msg? then l.queue.modify (·.push { sysid := f.sysid, compid := f.compid, msg := m })
  l.queue.modifyGet fun q => (q[0]?, q.extract 1)

/-- Send the messages of a tick as MAVLink 2 frames. -/
def send (l : Link) (tSec : Float) (out : Array Msg) : IO Unit := do
  if out.isEmpty then return
  let mut bufs : Array ByteArray := #[]
  for m in out do
    let seq ← l.seq.modifyGet fun s => (s, s + 1)
    let f := Frame.ofMsg seq l.sysid l.compid m
    bufs := bufs.push f.serialize
    l.logLine s!"{tSec} TX {l.sysid} {l.compid} {m.name} {toHex f.payload}"
  try (l.sock.sendAll bufs (some l.dst)).block
  catch e => IO.eprintln s!"send: {e}"

def close (l : Link) : IO Unit := do
  l.stop.set true
  if let some h := l.log then h.flush

end Link
