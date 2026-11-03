import Flight.Arith

/-!
# Shared data types

Vectors, Euler angles, and the two records exchanged with the external simulator. All world-frame
quantities use the north-east-down convention of ArduCopter: `x` north, `y` east, `z` down, so an
altitude of 5 m is `z = -5`. Body axes are forward-right-down, and Euler angles are ZYX
(yaw, then pitch, then roll), all in radians; body rates are `p, q, r` about the body axes in rad/s.

The controller state and step that compose the components live in `Flight.Controller`, because
they must import every component and the components import this file.
-/

namespace Flight

/-- A three-component vector over the scalar type `α`. -/
structure Vec3 (α : Type) where
  /-- First component (north in the world frame, forward or roll axis in the body frame). -/
  x : α
  /-- Second component (east in the world frame, right or pitch axis in the body frame). -/
  y : α
  /-- Third component (down in the world frame, down or yaw axis in the body frame). -/
  z : α
  deriving Repr

/-- Euler angles in the ZYX convention, in radians. -/
structure Euler (α : Type) where
  /-- Rotation about the body forward axis; positive is right side down. -/
  roll : α
  /-- Rotation about the body right axis; positive is nose up. -/
  pitch : α
  /-- Rotation about the down axis; positive is clockwise seen from above, `0` is north. -/
  yaw : α
  deriving Repr

namespace Vec3

variable {α : Type} [Arith α]

/-- The zero vector. -/
def zero : Vec3 α := ⟨0, 0, 0⟩

/-- Componentwise sum of two vectors. -/
instance : Add (Vec3 α) := ⟨fun a b => ⟨a.x + b.x, a.y + b.y, a.z + b.z⟩⟩

/-- Componentwise difference of two vectors. -/
instance : Sub (Vec3 α) := ⟨fun a b => ⟨a.x - b.x, a.y - b.y, a.z - b.z⟩⟩

/-- Componentwise negation of a vector. -/
instance : Neg (Vec3 α) := ⟨fun a => ⟨-a.x, -a.y, -a.z⟩⟩

/-- Multiplication of a vector by a scalar. -/
def smul (k : α) (a : Vec3 α) : Vec3 α := ⟨k * a.x, k * a.y, k * a.z⟩

/-- Euclidean inner product. -/
def dot (a b : Vec3 α) : α := a.x * b.x + a.y * b.y + a.z * b.z

/-- Squared Euclidean norm, which needs no square root. -/
def normSq (a : Vec3 α) : α := dot a a

/-- Euclidean norm. -/
def norm (a : Vec3 α) : α := Arith.sqrt (normSq a)

/-- Apply a scalar map to every component. -/
def map {β : Type} (f : α → β) (a : Vec3 α) : Vec3 β := ⟨f a.x, f a.y, f a.z⟩

end Vec3

/-- One sample sent by the simulator to the controller at every tick. -/
structure SimInput (α : Type) where
  /-- Position in the world frame, meters (NED). -/
  pos : Vec3 α
  /-- Velocity in the world frame, meters per second (NED). -/
  vel : Vec3 α
  /-- Attitude as ZYX Euler angles, radians. -/
  att : Euler α
  /-- Body angular rates `(p, q, r)`, radians per second. -/
  rates : Vec3 α
  /-- Time elapsed since the previous sample, seconds. -/
  dt : α
  deriving Repr

/-- The four normalized motor commands returned to the simulator, each in `[0, 1]`, numbered as in `Flight.Mixer`. -/
structure Motors (α : Type) where
  /-- Front-right motor, spinning counter-clockwise seen from above. -/
  m1 : α
  /-- Rear-left motor, spinning counter-clockwise seen from above. -/
  m2 : α
  /-- Front-left motor, spinning clockwise seen from above. -/
  m3 : α
  /-- Rear-right motor, spinning clockwise seen from above. -/
  m4 : α
  deriving Repr

end Flight
