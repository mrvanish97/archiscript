import ArchiScriptExamples.Monoidal

namespace ArchiScriptTests.MemberEnumeration
open ArchiScript ArchiScriptExamples.Monoidal

/-- Presentation enumeration order is independent of the VDP and its operations. -/
private def reversedBits : MemberEnumeration Bool where
  indices := [true, false]
  complete := by intro i; cases i <;> simp

#guard bit.memberIndices == [false, true]
#guard (letI : MemberEnumeration Bool := reversedBits
  bit.memberIndices) == [true, false]

-- Both enumeration choices range over the same type of member indices.
example (i : Bool) : i ∈ (letI : MemberEnumeration Bool := reversedBits
    bit.memberIndices) := by
  letI : MemberEnumeration Bool := reversedBits
  exact bit.memberIndices_complete i

-- The same operation can be used regardless of enumeration.
#guard (Operation.firstFiberConflict (Operation.id bit) (Operation.id bit)).isNone
#guard (letI : MemberEnumeration Bool := reversedBits
  (Operation.firstFiberConflict (Operation.id bit) (Operation.id bit)).isNone)

-- Tensor enumerations are computed outside their constituent VDP structures.
#guard (bit.tensor bit).memberIndices.length == 4

end ArchiScriptTests.MemberEnumeration
