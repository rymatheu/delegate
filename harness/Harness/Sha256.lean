/-! SHA-256 (FIPS 180-4), for the contract and result-file hashes and for recomputing a module's
code hash from its recorded inputs. -/

namespace Harness.Sha256

private def K : Array UInt32 := #[
  0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
  0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
  0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
  0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
  0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
  0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
  0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
  0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2]

private def H0 : Array UInt32 :=
  #[0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19]

@[inline] private def rotr (x : UInt32) (n : UInt32) : UInt32 := (x >>> n) ||| (x <<< (32 - n))

/-- One 64-byte block of `m` starting at `off`. -/
private def compress (h : Array UInt32) (m : ByteArray) (off : Nat) : Array UInt32 := Id.run do
  let mut w : Array UInt32 := Array.mkEmpty 64
  for i in [0:16] do
    let b := off + 4 * i
    w := w.push ((m[b]!.toUInt32 <<< 24) ||| (m[b+1]!.toUInt32 <<< 16) |||
                 (m[b+2]!.toUInt32 <<< 8) ||| m[b+3]!.toUInt32)
  for i in [16:64] do
    let x := w[i-15]!
    let y := w[i-2]!
    let s0 := rotr x 7 ^^^ rotr x 18 ^^^ (x >>> 3)
    let s1 := rotr y 17 ^^^ rotr y 19 ^^^ (y >>> 10)
    w := w.push (w[i-16]! + s0 + w[i-7]! + s1)
  let mut a := h[0]!
  let mut b := h[1]!
  let mut c := h[2]!
  let mut d := h[3]!
  let mut e := h[4]!
  let mut f := h[5]!
  let mut g := h[6]!
  let mut hh := h[7]!
  for i in [0:64] do
    let s1 := rotr e 6 ^^^ rotr e 11 ^^^ rotr e 25
    let ch := (e &&& f) ^^^ ((~~~e) &&& g)
    let t1 := hh + s1 + ch + K[i]! + w[i]!
    let s0 := rotr a 2 ^^^ rotr a 13 ^^^ rotr a 22
    let maj := (a &&& b) ^^^ (a &&& c) ^^^ (b &&& c)
    let t2 := s0 + maj
    hh := g
    g := f
    f := e
    e := d + t1
    d := c
    c := b
    b := a
    a := t1 + t2
  return #[h[0]! + a, h[1]! + b, h[2]! + c, h[3]! + d, h[4]! + e, h[5]! + f, h[6]! + g, h[7]! + hh]

private def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

/-- Lower-case hexadecimal, eight digits per word. -/
def wordsHex (ws : Array UInt32) : String := Id.run do
  let mut s := ""
  for w in ws do
    for k in [0:8] do
      s := s.push (hexDigit ((w >>> (UInt32.ofNat (28 - 4 * k))) &&& 0xf).toNat)
  return s

/-- SHA-256 of a byte string, as 64 lower-case hexadecimal digits. -/
def hashBytes (data : ByteArray) : String := Id.run do
  let len := data.size
  let mut m := data
  m := m.push 0x80
  while m.size % 64 != 56 do
    m := m.push 0
  let bits := len * 8
  for k in [0:8] do
    m := m.push (UInt8.ofNat ((bits >>> (8 * (7 - k))) % 256))
  let mut h := H0
  for blk in [0:m.size / 64] do
    h := compress h m (64 * blk)
  return wordsHex h

def hashString (s : String) : String := hashBytes s.toUTF8

def hashFile (p : System.FilePath) : IO String := do
  return hashBytes (← IO.FS.readBinFile p)

end Harness.Sha256
