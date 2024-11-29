import LeanCourse.Common
import Mathlib.Data.Complex.Exponential
open Real Function Set Nat

/-

* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapter 3, sections 2, 3, 5, 6.
  Read chapter 4, section 1.

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  There are solutions in the solution folder in case you get stuck.

* Hand in the solutions to the exercises below. Deadline: 29.10.2023.

* Make sure the file you hand-in compiles without error.
  Use `sorry` if you get stuck on an exercise.
-/


/-! # Exercises to practice. -/


example {p : ℝ → Prop} (h : ∀ x, p x) : ∃ x, p x := by {
  use 0
  exact h 0
  }


example {α : Type*} {p q : α → Prop} (h : ∀ x, p x → q x) :
    (∃ x, p x) → (∃ x, q x) := by {
  intro ⟨x, hpx⟩
  use x
  exact h x hpx
  }

/- Prove the following with basic tactics, without using `tauto` or lemmas from Mathlib. -/
example {α : Type*} {p : α → Prop} {r : Prop} :
    ((∃ x, p x) → r) ↔ (∀ x, p x → r) := by {
  constructor
  · intro h x hpx
    apply h
    use x
  · intro h1 ⟨x, hpx⟩
    exact h1 x hpx
  }

/- Prove the following with basic tactics, without using `tauto` or lemmas from Mathlib. -/
example {α : Type*} {p : α → Prop} {r : Prop} :
    (∃ x, p x ∧ r) ↔ ((∃ x, p x) ∧ r) := by {
  constructor
  · intro ⟨x, hpx, hr⟩
    constructor
    · use x
    · exact hr
  · intro ⟨⟨x, hpx⟩, hr⟩
    use x
  }

/- Prove the following without using `push_neg` or lemmas from Mathlib.
You will need to use `by_contra` in the proof. -/
example {α : Type*} (p : α → Prop) : (∃ x, p x) ↔ (¬ ∀ x, ¬ p x) := by {
  constructor
  · intro ⟨x, hpx⟩ h
    apply h x
    exact hpx
  · intro h1
    by_contra h2
    apply h1
    intro x hpx
    apply h2
    use x
  }

def SequentialLimit (u : ℕ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε

example (a : ℝ) : SequentialLimit (fun n : ℕ ↦ a) a := by {
  intro ε hε
  use 0
  intro n _
  rw [sub_self, abs_zero]
  exact hε
  }

/-
`(n)!` denotes the factorial function on the natural numbers.
The parentheses are mandatory when writing.
Use `calc` to prove this.
You can use `exact?` to find lemmas from the library,
such as the fact that factorial is monotone. -/
example (n m k : ℕ) (h : n ≤ m) : (n)! ∣ (m + 1)! := by {
  calc
    (n)! ∣ (m)! := by exact factorial_dvd_factorial h
    _ ∣ (m + 1) * (m)! := by exact Nat.dvd_mul_left (m)! (m + 1)
    _ ∣ (m + 1)! := by rfl
  }

section Set

variable {α β : Type*} {s t : Set α}

/- Prove the following statements about sets. -/

example {f : β → α} : f '' (f ⁻¹' s) ⊆ s := by {
  simp_rw [image, setOf_subset, mem_preimage]
  intro x ⟨a, has, hax⟩
  rw [← hax]
  exact has
  }

example {f : β → α} (h : Surjective f) : s ⊆ f '' (f ⁻¹' s) := by {
  intro x xmem
  rw [mem_image]
  obtain ⟨y, hy⟩ := h x
  use y
  rw [mem_preimage, hy]
  exact ⟨xmem, rfl⟩
  }

example {f : α → β} (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by {
  intro x
  simp_rw [mem_inter_iff, mem_image]
  intro ⟨⟨y1, y1mem, fy1⟩, ⟨y2, y2mem, fy2⟩⟩
  have : y1 = y2 := by
    apply h
    rw [fy1, fy2]
  subst y1
  use y2
  exact ⟨⟨y1mem, y2mem⟩, fy2⟩
  }

example {I : Type*} (f : α → β) (A : I → Set α) : (f '' ⋃ i, A i) = ⋃ i, f '' A i := by {
  ext x
  simp_rw [mem_image, mem_iUnion]
  constructor
  · intro ⟨y, ⟨⟨i, hi⟩, fxy⟩⟩
    use i, y
  · intro ⟨i, ⟨y, ⟨ymem, fyx⟩⟩⟩
    use y
    exact ⟨⟨i, ymem⟩, fyx⟩
  }

example : (fun x : ℝ ↦ x ^ 2) '' univ = { y : ℝ | y ≥ 0 } := by {
  ext x
  rw [mem_image, mem_setOf]
  constructor
  · intro ⟨y, _, yeq⟩
    rw [← yeq]
    exact sq_nonneg y
  · intro hx
    use sqrt x
    constructor
    · exact mem_univ _
    · exact sq_sqrt hx
  }

end Set

/-! # Exercises to hand-in. -/


/- Prove the following with basic tactics, without using `tauto` or lemmas from Mathlib. -/
lemma exists_distributes_over_or {α : Type*} {p q : α → Prop} :
    (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) := by {
  constructor
  · intro ⟨x, hx⟩
    rcases hx with hx | hx
    · left
      use x
    · right
      use x
  · intro h
    rcases h with h | h
    · obtain ⟨x, hx⟩ := h
      use x
      left
      exact hx
    · obtain ⟨x, hx⟩ := h
      use x
      right
      exact hx
  }

section Surjectivity

/- Lean's mathematical library knows what a surjective function is,
but let's define it here ourselves and prove some things about it. -/
def SurjectiveFunction (f : ℝ → ℝ) : Prop :=
  ∀ (y : ℝ), ∃ (x : ℝ), f x = y

variable {f g : ℝ → ℝ} {x : ℝ}

/- `rfl` or `simp` can compute the following.
`simp` is a very useful tactic that can simplify many expressions. -/
example : (g ∘ f) x = g (f x) := by simp

lemma surjective_composition (hf : SurjectiveFunction f) :
    SurjectiveFunction (g ∘ f) ↔ SurjectiveFunction g := by {
  constructor
  · intro h x
    obtain ⟨y, hy⟩ := h x
    use f y
    exact hy
  · intro hg
    intro x
    obtain ⟨y, hy⟩ := hg x
    obtain ⟨z, hz⟩ := hf y
    use z
    rw [← hy, ← hz]
    rfl
  }

/- When composing a surjective function by a linear function
to the left and the right, the result will still be a
surjective function. The `ring` tactic will be very useful here! -/
lemma surjective_linear (hf : SurjectiveFunction f) :
    SurjectiveFunction (fun x ↦ 2 * f (3 * (x + 4)) + 1) := by {
  intro y
  obtain ⟨x, hx⟩ := hf ((y - 1) / 2)
  use (x / 3 - 4)
  ring
  rw [hx]
  ring
  }

/- Let's prove Cantor's theorem:
there is no surjective function from any set to its power set.
Hint: use `let R := {x | x ∉ f x}` to consider the set `R` of elements `x`
that are not in `f x`
-/
lemma exercise_cantor (α : Type*) (f : α → Set α) : ¬ Surjective f := by {
  intro hf
  let R := {x | x ∉ f x}
  obtain ⟨x, hx⟩ := hf R
  by_cases h : x ∈ R
  · unfold R at h
    rw [mem_setOf] at h
    apply h
    rw [hx]
    unfold R
    exact h
  · apply h
    unfold R
    rw [← hx] at h
    exact h
  }

end Surjectivity

/- Prove that the sum of two converging sequences converges. -/
lemma sequentialLimit_add {s t : ℕ → ℝ} {a b : ℝ}
      (hs : SequentialLimit s a) (ht : SequentialLimit t b) :
    SequentialLimit (fun n ↦ s n + t n) (a + b) := by {
  intro ε hε
  obtain ⟨N1, hs⟩ :=  hs (ε / 2) (half_pos hε)
  obtain ⟨N2, ht⟩ := ht (ε / 2) (half_pos hε)
  use max N1 N2
  intro n nge
  calc
    |s n + t n - (a + b)| = |(s n - a) + (t n - b)| := by ring
    _ ≤ |s n - a| + |t n - b| := by exact abs_add_le (s n - a) (t n - b)
    _ < ε / 2 + ε / 2 := by
      gcongr
      · exact hs n (le_of_max_le_left nge)
      · exact ht n (le_of_max_le_right nge)
    _ = ε := by exact add_halves ε
  }

/- It may be useful to case split on whether `c = 0` is true. -/
lemma sequentialLimit_mul_const {s : ℕ → ℝ} {a : ℝ} (c : ℝ) (hs : SequentialLimit s a) :
    SequentialLimit (fun n ↦ c * s n) (c * a) := by {
  intro ε hε
  by_cases hc : c = 0
  · subst c
    use 0
    intro n _
    simp_rw [zero_mul, sub_self, abs_zero]
    exact hε
  · obtain ⟨N, hs⟩ := hs (ε / |c|) (by simp [hε, hc])
    use N
    intro n nge
    calc
      |c * s n - c * a| = |c * (s n - a)| := by ring
      _ = |c| * |s n - a| := by exact abs_mul c (s n - a)
      _ < |c| * (ε / |c|) := by
        gcongr
        exact hs n nge
      _ = ε  := by
        exact mul_div_cancel₀ ε (by exact abs_ne_zero.mpr hc)
  }





section Growth

variable {s t : ℕ → ℕ} {k : ℕ}

/- `simp` can help you simplify expressions like the following. -/
example : (fun n ↦ n * s n) k = k * s k := by simp
example (a b c : ℕ) : c ≥ max a b ↔ c ≥ a ∧ c ≥ b := by simp

/- Given two sequences of natural numbers `s` and `t`.
We say that `s` eventually grows faster than `t` if for all `k : ℕ`,
`s_n` will be at least as large as `k * t_n` for large enough `n`. -/
def EventuallyGrowsFaster (s t : ℕ → ℕ) : Prop :=
  ∀ k : ℕ, ∃ N : ℕ, ∀ n ≥ N, k * t n ≤ s n

/- show that `n * s n` grows (eventually) faster than `s n`. -/
lemma eventuallyGrowsFaster_mul_left :
    EventuallyGrowsFaster (fun n ↦ n * s n) s := by {
  intro k
  use k
  intro n ngek
  calc
    k * s n ≤ n * s n := by gcongr
    _ =  (fun n ↦ n * s n) n := rfl
  }

/- Show that if `sᵢ` grows eventually faster than `tᵢ` then
`s₁ + s₂` grows eventually faster than `t₁ + t₂`. -/
lemma eventuallyGrowsFaster_add {s₁ s₂ t₁ t₂ : ℕ → ℕ}
    (h₁ : EventuallyGrowsFaster s₁ t₁) (h₂ : EventuallyGrowsFaster s₂ t₂) :
    EventuallyGrowsFaster (s₁ + s₂) (t₁ + t₂) := by {
  intro k
  obtain ⟨N1, hN1⟩ := h₁ k
  obtain ⟨N2, hN2⟩ := h₂ k
  use max N1 N2
  intro n nge
  calc
    k * (t₁ + t₂) n = k * t₁ n + k * t₂ n := by simp [mul_add]
    _ ≤ s₁ n + s₂ n := by
      gcongr
      · exact hN1 n (le_of_max_le_left nge)
      · exact hN2 n (le_of_max_le_right nge)
    _ = (s₁ + s₂) n := rfl
  }

/- Find a positive function that grows faster than itself when shifted by one. -/
lemma eventuallyGrowsFaster_shift : ∃ (s : ℕ → ℕ),
    EventuallyGrowsFaster (fun n ↦ s (n+1)) s ∧ ∀ n, s n ≠ 0 := by {
  use fun n ↦ n ^ n
  constructor
  · intro k
    use k
    intro n nge
    calc
      k * n ^ n
      _ ≤ k * (n + 1) ^ n := by
        gcongr
        exact Nat.le_add_right n 1
      _ ≤ (n + 1) * (n + 1) ^ n := by
        gcongr
        linarith
      _ = (n + 1) ^ (n + 1) := by ring
  · intro n
    exact pow_self_ne_zero n
  }

end Growth
