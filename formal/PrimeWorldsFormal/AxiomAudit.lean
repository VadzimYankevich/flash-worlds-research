import PrimeWorldsFormal

namespace FlashWorlds

/-! This file is intentionally an audit, not an additional assumption. -/

/--
info: 'FlashWorlds.covered_iff_composite' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms covered_iff_composite

/--
info: 'FlashWorlds.mem_coveredFinset_iff_composite' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms mem_coveredFinset_iff_composite

/--
info: 'FlashWorlds.covered_stable' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms covered_stable

/--
info: 'FlashWorlds.coveredFinset_stable' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms coveredFinset_stable

/--
info: 'FlashWorlds.executable_hole_count_eq_prime_count' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms executable_hole_count_eq_prime_count

end FlashWorlds
