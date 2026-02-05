import VerifiedAgora.tagger

namespace AgoraInformationTheory

@[target]
theorem one_plus_one : 1 + 1 = 2 := rfl

@[target]
theorem two_eq_two : 2 = 2 := rfl

@[target]
theorem zero_add (n : Nat) : 0 + n = n := Nat.zero_add n

@[target]
theorem add_zero (n : Nat) : n + 0 = n := Nat.add_zero n

@[target]
theorem nat_succ_eq_add_one (n : Nat) : Nat.succ n = n + 1 := rfl

end AgoraInformationTheory
