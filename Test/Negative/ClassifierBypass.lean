-- EXPECT: `classify` is not a field
import ArchiScript.Partition
open ArchiScript
def bypass : VDP where
  Carrier := Bool
  MemberIndex := Bool
  classify := id
