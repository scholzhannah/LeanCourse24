import LeanCourse.Common
import Mathlib.Data.Complex.Exponential
noncomputable section
open Real Function Set Nat
open Classical


/-

* From Mathematics in Lean https://leanprover-community.github.io/mathematics_in_lean
  Read chapter 4, sections 2, 3.

* Do the exercises corresponding to these sections in the `LeanCourse/MIL` folder.
  There are solutions in the solution folder in case you get stuck.

* Hand in the solutions to the exercises below. Deadline: 5.11.

* Make sure the file you hand-in compiles without error.
  Use `sorry` if you get stuck on an exercise.
-/


/-! # Exercises to practice. -/

/- Do the exercises about sets from last exercise set, if you haven't done them because
we didn't cover the material in class yet. -/


variable {α β γ ι : Type*} (f : α → β) (x : α) (s : Set α)

/- Prove this equivalence for sets. -/
example : s = univ ↔ ∀ x : α, x ∈ s := by {
  exact eq_univ_iff_forall
  }


/- Prove the law of excluded middle without using `by_cases`/`tauto` or lemmas from the library.
You will need to use `by_contra` in the proof. -/
lemma exercise3_1 (p : Prop) : p ∨ ¬ p := by {
  by_contra h
  push_neg at h
  apply h.1
  exact h.2
  }

/- `α × β` is the cartesian product of the types `α` and `β`.
Elements of the cartesian product are denoted `(a, b)`, and the projections are `.1` and `.2`.
As an example, here are two ways to state when two elements of the cartesian product are equal.
You can use the `ext` tactic to show that two pairs are equal.
`simp` can simplify `(a, b).1` to `a`.
This is true by definition, so calling `assumption` below also works directly. -/

example (a a' : α) (b b' : β) : (a, b) = (a', b') ↔ a = a' ∧ b = b' := Prod.ext_iff
example (x y : α × β) : x = y ↔ x.1 = y.1 ∧ x.2 = y.2 := Prod.ext_iff
example (a a' : α) (b b' : β) (ha : a = a') (hb : b = b') : (a, b) = (a', b') := by
  ext
  · simp
    assumption
  · assumption

/- To practice, show the equality of the following pair. What is the type of these pairs? -/
example (x y : ℝ) : (123 + 32 * 3, (x + y) ^ 2) = (219, x ^ 2 + 2 * x * y + y ^ 2) := by {
  rw [Prod.ext_iff]
  constructor
  · norm_num
  · ring
  }

/- `A ≃ B` means that there is a bijection from `A` to `B`.
So in this exercise you are asked to prove that there is a bijective correspondence between
  functions from `ℤ × ℕ` to `ℤ × ℤ`
and
  functions from `ℕ` to `ℕ`
This is an exercise about finding lemmas from the library.
Your proof is supposed to only combine results from the library,
you are not supposed to define the bijection yourself.
If you want, you can use `calc` blocks with `≃`. -/
example : (ℤ × ℕ → ℤ × ℤ) ≃ (ℕ → ℕ) := by {
  apply Equiv.arrowCongr
  · exact Denumerable.eqv (ℤ × ℕ)
  · exact Denumerable.eqv (ℤ × ℤ)
  }

/- Prove a version of the axiom of choice Lean's `Classical.choose`. -/
example (C : ι → Set α) (hC : ∀ i, ∃ x, x ∈ C i) : ∃ f : ι → α, ∀ i, f i ∈ C i := by {
  let f := fun i ↦ Classical.choose (hC i)
  have hf := fun i ↦ Classical.choose_spec (hC i)
  use f
  }


/-! # Exercises to hand-in. -/


/- ## Converging sequences

Prove two more lemmas about converging sequences. -/

/-- From the lecture, the sequence `u` of real numbers converges to `l`. -/
def SequentialLimit (u : ℕ → ℝ) (l : ℝ) : Prop :=
  ∀ ε > 0, ∃ N, ∀ n ≥ N, |u n - l| < ε

/- Let's prove that reindexing a convergent sequence
by a reindexing function that tends to infinity
produces a sequence that converges to the same value. -/
lemma sequentialLimit_reindex {s : ℕ → ℝ} {r : ℕ → ℕ} {a : ℝ}
    (hs : SequentialLimit s a) (hr : ∀ m : ℕ, ∃ N : ℕ, ∀ n ≥ N, r n ≥ m) :
    SequentialLimit (s ∘ r) a := by {
  intro ε hε
  obtain ⟨N', hN'⟩ := hs ε hε
  obtain ⟨N, hN⟩ := hr N'
  use N
  intro n ngeN
  apply hN'
  exact hN n ngeN
  }


/- Let's prove the squeeze theorem for sequences.
You will want to use the lemma in the library that states
`|a| < b ↔ -b < a ∧ a < b`. -/
lemma sequentialLimit_squeeze {s₁ s₂ s₃ : ℕ → ℝ} {a : ℝ}
    (hs₁ : SequentialLimit s₁ a) (hs₃ : SequentialLimit s₃ a)
    (hs₁s₂ : ∀ n, s₁ n ≤ s₂ n) (hs₂s₃ : ∀ n, s₂ n ≤ s₃ n) :
    SequentialLimit s₂ a := by {
  intro ε hε
  obtain ⟨N₁, hN₁⟩ := hs₁ ε hε
  obtain ⟨N₃, hN₃⟩ := hs₃ ε hε
  use max N₁ N₃
  intro n nge
  rw [abs_sub_lt_iff]
  constructor
  · calc
      s₂ n - a ≤ s₃ n - a := tsub_le_tsub_right (hs₂s₃ n) a
      _ < ε := by
        specialize hN₃ n (le_of_max_le_right nge)
        exact lt_of_abs_lt hN₃
  · calc
      a - s₂ n ≤ a - s₁ n := tsub_le_tsub_left (hs₁s₂ n) a
      _ < ε := by
        specialize hN₁ n (le_of_max_le_left nge)
        exact (abs_sub_lt_iff.1 hN₁).2
  }

/- ## Sets -/

/- Prove this without using lemmas from Mathlib. -/
lemma image_and_intersection {α β : Type*} (f : α → β) (s : Set α) (t : Set β) :
    f '' s ∩ t = f '' (s ∩ f ⁻¹' t) := by {
  ext x
  simp only [mem_inter_iff, mem_image, mem_preimage] -- Floris said these lemmas were fine
  constructor
  · intro ⟨⟨y, ymems, fyx⟩, xmemt⟩
    subst x
    use y
  · intro ⟨y, ⟨ymems, fymems⟩, fyx⟩
    subst x
    constructor
    · use y
    · exact fymems
  }

/- Prove this by finding relevant lemmas in Mathlib. -/
lemma preimage_square :
    (fun x : ℝ ↦ x ^ 2) ⁻¹' {y | y ≥ 16} = { x : ℝ | x ≤ -4 } ∪ { x : ℝ | x ≥ 4 } := by {
  ext x
  simp only [ge_iff_le, preimage_setOf_eq, mem_setOf_eq, mem_union]
  calc
    16 ≤ x ^ 2 ↔ 4 ^ 2 ≤ x ^ 2 := by norm_num
    _ ↔ |4| ≤ |x| := sq_le_sq
    _ ↔ 4 ≤ |x| := by norm_num
    _ ↔ x ≤ -4 ∨ 4 ≤ x := le_abs'
  }


/- `InjOn` states that a function is injective when restricted to `s`.
`LeftInvOn g f s` states that `g` is a left-inverse of `f` when restricted to `s`.
Now prove the following example, mimicking the proof from the lecture.
If you want, you can define `g` separately first.
-/
lemma inverse_on_a_set [Inhabited α] (hf : InjOn f s) : ∃ g : β → α, LeftInvOn g f s := by {
  use fun b ↦ if h : ∃ a ∈ s, f a = b then Classical.choose h else default
  intro x xmems
  have h : ∃ a ∈ s, f a = f x := by use x
  have hx := Classical.choose_spec h
  refine hf ?_ xmems ?_
  · simp [h, hx]
  · simp [h, hx]
  }


/- Let's prove that if `f : α → γ` and `g : β → γ` are injective function whose
ranges partition `γ`, then `Set α × Set β` is in bijective correspondence to `Set γ`.

To help you along the way, some potentially useful ways to reformulate the hypothesis are given. -/

-- This lemma might be useful.
#check Injective.eq_iff

lemma set_bijection_of_partition {f : α → γ} {g : β → γ} (hf : Injective f) (hg : Injective g)
    (h1 : range f ∩ range g = ∅) (h2 : range f ∪ range g = univ) :
    ∃ (L : Set α × Set β → Set γ) (R : Set γ → Set α × Set β), L ∘ R = id ∧ R ∘ L = id := by {
  -- h1' and h1'' might be useful later as arguments of `simp` to simplify your goal.
  have h1' : ∀ x y, f x ≠ g y := by
    intro x y fxeqgy
    rw [← mem_empty_iff_false (f x), ← h1]
    constructor
    · exact mem_range_self x
    · rw [fxeqgy]
      exact mem_range_self y
  have h1'' : ∀ y x, g y ≠ f x := fun y x a ↦ h1' x y (id (Eq.symm a))
  have h2' : ∀ x, x ∈ range f ∪ range g := by
    rw [h2]
    intro
    trivial
  let L : Set α × Set β → Set γ := fun ⟨a, b⟩ ↦ f '' a ∪ g '' b
  let R : Set γ → Set α × Set β := fun c ↦ ⟨(f ⁻¹' c), (g ⁻¹' c)⟩
  use L, R
  unfold L R
  repeat rw [Function.funext_iff]
  constructor
  · intro x
    simp only [comp_apply, id_eq]
    apply subset_antisymm
    · apply union_subset
      · exact image_preimage_subset f x
      · exact image_preimage_subset g x
    · intro y ymemx
      rcases h2' y with h | h
      · left
        obtain ⟨z, hz⟩ := h
        simp
        use z
        subst y
        simp [ymemx]
      · right
        obtain ⟨z, hz⟩ := h
        simp
        use z
        subst y
        simp [ymemx]
  · intro x
    simp
    rw [Prod.eq_iff_fst_eq_snd_eq]
    constructor
    · have : f ⁻¹' (g '' x.2) = ∅ := by
        rw [preimage_eq_empty_iff]
        apply disjoint_of_subset_left (u := range g) (image_subset_range g x.2)
        rw [disjoint_iff_inter_eq_empty, inter_comm, h1]
      rw [this]
      simp [hf]
    · have : g ⁻¹' (f '' x.1) = ∅ := by
        rw [preimage_eq_empty_iff]
        apply disjoint_of_subset_left (u := range f) (image_subset_range f x.1)
        rw [disjoint_iff_inter_eq_empty, h1]
      rw [this]
      simp [hg]
  }
