import Paperproof
import Mathlib

set_option linter.style.multiGoal false

theorem one_not_eq_two : 1 ≠ 2 := by norm_num

lemma three_n_plus_two_even_if_n_even (n : ℤ) : Even (3 * n + 2) → Even n := by
  intro h
  by_contra n_odd

  have n_odd : Odd n := Int.not_even_iff_odd.mp n_odd

  have three_n_even : Even (3 * n) := by
    have : Even (3 * n + 2 - 2) := Even.sub h even_two
    simp at this
    exact this

  have two_n_even : Even (2 * n) := even_two_mul n

  have two_n_not_even : ¬Even (2 * n) := by
    have two_n_eq : 3 * n - n = 2 * n := by ring
    have := three_n_even.sub_odd n_odd
    rw [two_n_eq] at this
    exact Int.not_even_iff_odd.mpr this

  exact absurd two_n_even two_n_not_even

theorem absorption (p q : Prop) : (p ∧ (p ∨ q)) ↔ p := by
  constructor
  · intro h; exact h.left
  · intro hp
    constructor
    · exact hp
    · left; exact hp

theorem hyp_syllogism (p q r : Prop) (h₁ : p → q) (h₂ : (q → r)) : p → r := by
  intro hp
  exact h₂ (h₁ hp)

theorem disj_syllogism (p q : Prop) (h₁ : p ∨ q) (h₂ : ¬p) : q := by
  rcases h₁ with hp | hq
  · exact absurd hp h₂
  · exact hq

theorem disj_mp (p q r s : Prop) (h : (p → q) ∧ (r → s) ∧ (p ∨ r)) : q ∨ s := by
  rcases h with ⟨hpq, hrs, hpr⟩
  rcases hpr with hp | hr
  · left; exact hpq hp
  · right; exact hrs hr

theorem disj_mt (p q r s : Prop) (h : (p → q) ∧ (r → s) ∧ (¬q ∨ ¬s)) : ¬p ∨ ¬r := by
  rcases h with ⟨hpq, hrs, hqs⟩
  rcases hqs with hnq | hns
  · left; intro hp; exact hnq (hpq hp)
  · right; intro hr; exact hns (hrs hr)

theorem mpt (p q : Prop) (h₁ : ¬(p ∧ q)) (h₂ : p) : ¬q := by
  intro hq
  exact h₁ ⟨h₂, hq⟩

lemma and_or_distrib_left (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  constructor
  intro h

  rcases h with ⟨hp, hqr⟩
  rcases hqr with hq | hr
  · left; constructor; assumption; assumption
  · right; constructor; assumption; assumption

  intro h
  rcases h with hpq | hpr
  · rcases hpq with ⟨hp, hq⟩
    · constructor; assumption; left; assumption
  · rcases hpr with ⟨hp, hr⟩
    · constructor; assumption; right; assumption

lemma P2B7 (p q : Prop) : ((p ∨ (¬p ∧ q)) ∨ (p ∨ ¬q)) ↔ True := by
  constructor
  · intro; trivial
  · intro
    rcases (em p) with hp | hnp
    · left; left; assumption
    · rcases (em q) with hq | hnq
      · left; right; exact ⟨hnp, hq⟩
      · right; right; assumption


lemma P2B8 (p q : Prop) : ((q ∨ (¬p ∧ q) ∨ (p ∨ ¬q)) ∧ ¬q) ↔ ¬q := by
  constructor
  · intro h
    exact h.2
  · intro hnq
    constructor
    · rcases (em p) with hp | hnp
      · right; right; left; exact hp
      · right; right; right; exact hnq
    · exact hnq

lemma P3B5 (p q r : Prop) : ((p → ¬q) ∧ (¬q → ¬r) ∧ p) → ¬r := by
  intro h
  rcases h with ⟨h1, h2, hp⟩
  exact hyp_syllogism p (¬q) (¬r) h1 h2 hp

lemma P3C7 (p q r s : Prop) : ((p → r) ∧ (¬p → q) ∧ (q → s)) → (¬r → s) := by
  intro ⟨hpr, hnpq, hqs⟩ hnr
  have hnps := hyp_syllogism (¬p) q s hnpq hqs
  have hrs := disj_mp p r (¬p) s ⟨hpr, hnps, em p⟩
  exact disj_syllogism r s hrs hnr

lemma P3C8 (p q r s u w : Prop) : ((p → q) ∧ (q → (r ∧ s)) ∧ (p ∧ w) ∧ (¬r ∨ (¬w ∨ u))) → u := by
  intro h
  rcases h with ⟨h1, h2, h3, h4⟩
  rcases h3 with ⟨hp, hw⟩
  rcases h2 (h1 hp) with ⟨hr, _⟩
  have h5 := disj_syllogism (¬r) (¬w ∨ u) h4 (not_not.mpr hr)
  exact disj_syllogism (¬w) u h5 (not_not.mpr hw)

lemma P2A1 (p q : Prop) : ((¬p ∧ q) → q) ↔ True := by
  constructor
  · intro; trivial
  · intro _ h; exact h.right

lemma P2A3 (p q : Prop) : Xor' (¬p ∨ q) (p → q) ↔ False := by
  rw [xor_def]
  constructor
  · intro h
    rcases h with ⟨h1, h2⟩ | ⟨h3, h4⟩
    · apply h2
      intro hp
      rcases h1 with hnp | hq
      · exact absurd hp hnp
      · exact hq
    · apply h4
      rcases (em p) with hp | hnp
      · right; exact h3 hp
      · left; exact hnp
  · exact False.elim

lemma P2A3_simp (p q : Prop) : Xor' (¬p ∨ q) (p → q) = False := by
  simp only [xor_def, imp_iff_not_or, and_not_self, or_self]

lemma P2A4 (p q : Prop) : ((p ∧ q) → p) ↔ True := by
  constructor
  · intro; trivial
  · intro _ h; exact h.left

lemma P2A5 (p q : Prop) : (p → (p ∨ q)) ↔ True := by
  constructor
  · intro; trivial
  · intro _ h; left; exact h

lemma P2A5_simp (p q : Prop) : (p → (p ∨ q)) = True := by
  simp; intro hp; left; exact hp

lemma P2B15 (p q : Prop) : (¬((¬p ∧ q) ∨ (¬p ∧ ¬q)) ∨ (p ∧ q)) ↔ p := by
  constructor
  · intro h
    rcases h with h1 | hpq
    · rcases (em p) with hp | hnp
      · exact hp
      · exfalso
        apply h1
        rcases (em q) with hq | hnq
        · left; exact ⟨hnp, hq⟩
        · right; exact ⟨hnp, hnq⟩
    · exact hpq.left
  · intro hp
    left
    intro h
    rcases h with ⟨hnp, _⟩ | ⟨hnp, _⟩
    · exact hnp hp
    · exact hnp hp

lemma P2B15_simp (p q : Prop) : (¬((¬p ∧ q) ∨ (¬p ∧ ¬q)) ∨ (p ∧ q)) = p := by
  simp
  constructor
  · intro h
    rcases h with ⟨h1, h2⟩ | ⟨hp, _⟩
    · rcases (em p) with hp | hnp
      · exact hp
      · exact absurd (h1 hnp) (not_not.mpr (h2 hnp))
    · exact hp
  · intro hp
    rcases (em q) with hq | hnq
    · right; exact ⟨hp, hq⟩
    · left
      constructor
      · intro hp' hq; exact hnq hq
      · intro hp'; exact absurd hp hp'

lemma P2B14 (p q : Prop) : (p ∧ (¬q ∨ p)) ↔ p := by
  rw [or_comm]
  exact absorption p (¬q)

lemma Q5 (n : ℕ) : Even (n) ↔ Even (n ^ 3) := by
  constructor
  · intro h
    rcases h with ⟨m, hm⟩
    use 4 * m^3
    rw [hm]
    ring
  · intro h_even
    by_contra h_not_even
    have h_odd : Odd (n ^ 3) := Odd.pow (Nat.not_even_iff_odd.mp h_not_even)
    exact (Nat.not_even_iff_odd.mpr h_odd) h_even

example (p q : Prop) : ((p ∧ q) → (p ∨ q)) ↔ True := by
  constructor
  · intro; trivial
  · intro _ h; left; exact h.left
