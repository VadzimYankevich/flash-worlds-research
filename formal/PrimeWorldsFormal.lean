import Init.Omega
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Order.Interval.Finset.Nat

/-!
  Formal core for the finite odd world from \`flash-worlds-research\`.

  There are two deliberately separate representations:
  * \`Covered\` is the factorisation relation stated in the paper;
  * \`coveredFinset\` is the executable finite product of axes and multipliers.
  Their equivalence is proved below.  Neither is defined by primality or
  compositeness.
-/

namespace FlashWorlds

def frontier (B : ℕ) : ℕ := min (B ^ 2) (3 * B + 4)

def Covered (B n : ℕ) : Prop :=
  ∃ p m : ℕ,
    Nat.Prime p ∧ Odd p ∧ p ≤ B ∧
      Odd m ∧ 3 ≤ m ∧ m ≤ B ∧ n = p * m

def SafeOdd (B n : ℕ) : Prop :=
  3 ≤ n ∧ n ≤ frontier B ∧ Odd n

def Composite (n : ℕ) : Prop := 2 ≤ n ∧ ¬ Nat.Prime n

/-- Bounded, odd prime axes.  The lower bound \`2\` follows from primality. -/
def finitePrimeAxes (B : ℕ) : Finset ℕ :=
  (Finset.Icc 2 B).filter fun p => Nat.Prime p ∧ Odd p

def finiteOddMultipliers (B : ℕ) : Finset ℕ :=
  (Finset.Icc 3 B).filter Odd

/-- The executable finite world \`S_B\`: duplicates of a product are removed. -/
def coveredFinset (B : ℕ) : Finset ℕ :=
  ((finitePrimeAxes B) ×ˢ (finiteOddMultipliers B)).image
    (fun pm : ℕ × ℕ => pm.1 * pm.2)

theorem mem_finitePrimeAxes {B p : ℕ} :
    p ∈ finitePrimeAxes B ↔ Nat.Prime p ∧ Odd p ∧ p ≤ B := by
  constructor
  · intro hp
    unfold finitePrimeAxes at hp
    rcases Finset.mem_filter.mp hp with ⟨hpIcc, hpred⟩
    rcases hpred with ⟨hpprime, hpodd⟩
    rcases Finset.mem_Icc.mp hpIcc with ⟨hp2, hpB⟩
    exact ⟨hpprime, hpodd, hpB⟩
  · rintro ⟨hpprime, hpodd, hpB⟩
    unfold finitePrimeAxes
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_Icc.mpr ⟨hpprime.two_le, hpB⟩, ⟨hpprime, hpodd⟩⟩

theorem mem_finiteOddMultipliers {B m : ℕ} :
    m ∈ finiteOddMultipliers B ↔ Odd m ∧ 3 ≤ m ∧ m ≤ B := by
  constructor
  · intro hm
    unfold finiteOddMultipliers at hm
    rcases Finset.mem_filter.mp hm with ⟨hmIcc, hmodd⟩
    rcases Finset.mem_Icc.mp hmIcc with ⟨hm3, hmB⟩
    exact ⟨hmodd, hm3, hmB⟩
  · rintro ⟨hmodd, hm3, hmB⟩
    unfold finiteOddMultipliers
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hm3, hmB⟩, hmodd⟩

/-- The finite product representation is exactly the factorisation relation. -/
theorem mem_coveredFinset_iff_Covered {B n : ℕ} :
    n ∈ coveredFinset B ↔ Covered B n := by
  constructor
  · intro hn
    unfold coveredFinset at hn
    rcases Finset.mem_image.mp hn with ⟨⟨p, m⟩, hpair, hmul⟩
    rcases Finset.mem_product.mp hpair with ⟨hp, hm⟩
    rcases mem_finitePrimeAxes.mp hp with ⟨hpprime, hpodd, hpB⟩
    rcases mem_finiteOddMultipliers.mp hm with ⟨hmodd, hm3, hmB⟩
    exact ⟨p, m, hpprime, hpodd, hpB, hmodd, hm3, hmB,
      by simpa using hmul.symm⟩
  · rintro ⟨p, m, hpprime, hpodd, hpB, hmodd, hm3, hmB, hnm⟩
    unfold coveredFinset
    apply Finset.mem_image.mpr
    refine ⟨(p, m), ?_, ?_⟩
    · exact Finset.mem_product.mpr
        ⟨mem_finitePrimeAxes.mpr ⟨hpprime, hpodd, hpB⟩,
          mem_finiteOddMultipliers.mpr ⟨hmodd, hm3, hmB⟩⟩
    · simpa using hnm.symm

private theorem odd_gap_two {a b : ℕ}
    (ha : Odd a) (hb : Odd b) (hab : a < b) : a + 2 ≤ b := by
  rcases ha with ⟨i, hi⟩
  rcases hb with ⟨j, hj⟩
  omega

theorem covered_is_composite {B n : ℕ}
    (hn3 : 3 ≤ n) (hcov : Covered B n) : Composite n := by
  rcases hcov with ⟨p, m, hp, hpodd, hpB, hmodd, hm3, hmB, hnm⟩
  constructor
  · omega
  · intro hnprime
    rcases hnprime.eq_one_or_self_of_dvd p ⟨m, hnm⟩ with hpone | hpn
    · exact hp.ne_one hpone
    · have hmul : p * 1 = p * m := by
        calc
          p * 1 = p := by simp
          _ = n := hpn
          _ = p * m := hnm
      have hmone : 1 = m := Nat.eq_of_mul_eq_mul_left hp.pos hmul
      omega

/-- Exact finite-world coverage on its certified odd window. -/
theorem covered_iff_composite {B n : ℕ}
    (hBodd : Odd B) (_hB3 : 3 ≤ B) (hn : SafeOdd B n) :
    Covered B n ↔ Composite n := by
  constructor
  · exact covered_is_composite hn.1
  · rintro ⟨hn2, hnprime⟩
    obtain ⟨m, hnm⟩ := Nat.minFac_dvd n
    have hn_ne_one : n ≠ 1 := by omega
    have hpprime : Nat.Prime n.minFac := Nat.minFac_prime hn_ne_one
    have hpodd : Odd n.minFac := by
      rcases Nat.even_or_odd n.minFac with hpeven | hpodd
      · exact (hn.2.2.not_two_dvd_nat
          (hpeven.two_dvd.trans (Nat.minFac_dvd n))).elim
      · exact hpodd
    have hmodd : Odd m := by
      rcases Nat.even_or_odd m with hmeven | hmodd
      · exact (hn.2.2.not_two_dvd_nat (by
          rw [hnm]
          exact hmeven.two_dvd.mul_left n.minFac)).elim
      · exact hmodd
    have hpB : n.minFac ≤ B := by
      apply (Nat.pow_le_pow_iff_left (by omega : (2 : ℕ) ≠ 0)).mp
      exact le_trans (Nat.minFac_sq_le_self (by omega) hnprime)
        (le_trans hn.2.1 (min_le_left _ _))
    have hm_ne_zero : m ≠ 0 := by
      intro hmzero
      have : n = 0 := by simpa [hmzero] using hnm
      omega
    have hm_ne_one : m ≠ 1 := by
      intro hmone
      apply hnprime
      have : n = n.minFac := by simpa [hmone] using hnm
      rw [this]
      exact hpprime
    have hm_ne_two : m ≠ 2 := by
      intro hmtwo
      subst m
      exact hmodd.not_two_dvd_nat (dvd_refl 2)
    have hm3 : 3 ≤ m := by omega
    have hp_ne_two : n.minFac ≠ 2 := by
      intro hptwo
      apply hpodd.not_two_dvd_nat
      simp [hptwo]
    have hp3 : 3 ≤ n.minFac := by
      have := hpprime.two_le
      omega
    have hmB : m ≤ B := by
      by_contra hnot
      have hBm : B < m := by omega
      have hgap : B + 2 ≤ m := odd_gap_two hBodd hmodd hBm
      have hlarge : 3 * (B + 2) ≤ n.minFac * m := Nat.mul_le_mul hp3 hgap
      have hnmax : n ≤ 3 * B + 4 := le_trans hn.2.1 (min_le_right _ _)
      have htoo_large : 3 * B + 4 < n := by
        calc
          3 * B + 4 < 3 * (B + 2) := by omega
          _ ≤ n.minFac * m := hlarge
          _ = n := hnm.symm
      exact (not_lt_of_ge hnmax) htoo_large
    exact ⟨n.minFac, m, hpprime, hpodd, hpB, hmodd, hm3, hmB, hnm⟩

/-- The executable \`coveredFinset\` has the same certified-window exactness. -/
theorem mem_coveredFinset_iff_composite {B n : ℕ}
    (hBodd : Odd B) (hB3 : 3 ≤ B) (hn : SafeOdd B n) :
    n ∈ coveredFinset B ↔ Composite n :=
  mem_coveredFinset_iff_Covered.trans (covered_iff_composite hBodd hB3 hn)

theorem covered_mono {B B' n : ℕ} (hBB' : B ≤ B') :
    Covered B n → Covered B' n := by
  rintro ⟨p, m, hp, hpodd, hpB, hmodd, hm3, hmB, hnm⟩
  exact ⟨p, m, hp, hpodd, hpB.trans hBB', hmodd, hm3, hmB.trans hBB', hnm⟩

/-- Exact inheritance on the fixed old certified odd window. -/
theorem covered_stable {B B' n : ℕ}
    (hBodd : Odd B) (hB3 : 3 ≤ B) (hBB' : B ≤ B')
    (hn3 : 3 ≤ n) (hnG : n ≤ frontier B) (hnodd : Odd n) :
    Covered B' n ↔ Covered B n := by
  constructor
  · intro hcov
    apply (covered_iff_composite hBodd hB3 ⟨hn3, hnG, hnodd⟩).mpr
    exact covered_is_composite hn3 hcov
  · exact covered_mono hBB'

/-- The finite executable occupancy is stable on the old certified odd window. -/
theorem coveredFinset_stable {B B' n : ℕ}
    (hBodd : Odd B) (hB3 : 3 ≤ B) (hBB' : B ≤ B')
    (hn3 : 3 ≤ n) (hnG : n ≤ frontier B) (hnodd : Odd n) :
    n ∈ coveredFinset B' ↔ n ∈ coveredFinset B := by
  constructor
  · intro hn
    apply mem_coveredFinset_iff_Covered.mpr
    apply (covered_stable hBodd hB3 hBB' hn3 hnG hnodd).mp
    exact mem_coveredFinset_iff_Covered.mp hn
  · intro hn
    apply mem_coveredFinset_iff_Covered.mpr
    apply (covered_stable hBodd hB3 hBB' hn3 hnG hnodd).mpr
    exact mem_coveredFinset_iff_Covered.mp hn

def safeOddWindow (B : ℕ) : Finset ℕ :=
  (Finset.Icc 3 (frontier B)).filter Odd

def executableHoles (B : ℕ) : Finset ℕ :=
  (safeOddWindow B).filter fun n => n ∉ coveredFinset B

def primesInWindow (B : ℕ) : Finset ℕ :=
  (safeOddWindow B).filter Nat.Prime

theorem mem_safeOddWindow {B n : ℕ} :
    n ∈ safeOddWindow B ↔ SafeOdd B n := by
  constructor
  · intro hn
    unfold safeOddWindow at hn
    rcases Finset.mem_filter.mp hn with ⟨hnIcc, hnodd⟩
    rcases Finset.mem_Icc.mp hnIcc with ⟨hn3, hnG⟩
    exact ⟨hn3, hnG, hnodd⟩
  · rintro ⟨hn3, hnG, hnodd⟩
    unfold safeOddWindow
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hn3, hnG⟩, hnodd⟩

/-- Membership in the executable counter has the logical hole meaning. -/
theorem mem_executableHoles {B n : ℕ} :
    n ∈ executableHoles B ↔ SafeOdd B n ∧ ¬ Covered B n := by
  constructor
  · intro hn
    unfold executableHoles at hn
    rcases Finset.mem_filter.mp hn with ⟨hnwindow, hnnotcovered⟩
    refine ⟨mem_safeOddWindow.mp hnwindow, ?_⟩
    intro hcovered
    exact hnnotcovered (mem_coveredFinset_iff_Covered.mpr hcovered)
  · rintro ⟨hwindow, hnnotcovered⟩
    unfold executableHoles
    apply Finset.mem_filter.mpr
    refine ⟨mem_safeOddWindow.mpr hwindow, ?_⟩
    intro hncovered
    exact hnnotcovered (mem_coveredFinset_iff_Covered.mp hncovered)

/-- The executable holes and actual primes are the same finite set. -/
theorem executableHoles_eq_primes {B : ℕ} (hBodd : Odd B) (hB3 : 3 ≤ B) :
    executableHoles B = primesInWindow B := by
  apply Finset.ext
  intro n
  constructor
  · intro hn
    rcases mem_executableHoles.mp hn with ⟨hsafe, hnnotcovered⟩
    unfold primesInWindow
    apply Finset.mem_filter.mpr
    refine ⟨mem_safeOddWindow.mpr hsafe, ?_⟩
    by_contra hnprime
    apply hnnotcovered
    apply (covered_iff_composite hBodd hB3 hsafe).mpr
    have hn3 : 3 ≤ n := hsafe.1
    exact ⟨by omega, hnprime⟩
  · intro hn
    unfold primesInWindow at hn
    rcases Finset.mem_filter.mp hn with ⟨hnwindow, hnprime⟩
    apply mem_executableHoles.mpr
    refine ⟨mem_safeOddWindow.mp hnwindow, ?_⟩
    intro hncovered
    exact ((covered_iff_composite hBodd hB3
      (mem_safeOddWindow.mp hnwindow)).mp hncovered).2 hnprime

/-- The requested exact finite counter equality. -/
theorem executable_hole_count_eq_prime_count {B : ℕ}
    (hBodd : Odd B) (hB3 : 3 ≤ B) :
    (executableHoles B).card = (primesInWindow B).card :=
  congrArg Finset.card (executableHoles_eq_primes hBodd hB3)

end FlashWorlds
