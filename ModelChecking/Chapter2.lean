import ModelChecking.Mathlib

open Classical

-- Definition 2.1
structure TransSys where 
  S : Type _
  Act : Type _
  trans : S → Act → S → Prop
  I : Set S
  AP : Type _
  L : S → Set AP

notation s " -[" t ", " α "]→ " s' => TransSys.trans t s α s'

namespace TransSys 

variable (t : TransSys)

-- Page 20
def finite : Prop := sorry

-- Definition 2.3
def post₁ (s : t.S) (α : t.Act) : Set t.S := { s' | s -[t, α]→ s' }

-- Definition 2.3
def post₂ (s : t.S) : Set t.S := { s' | ∃ α, s' ∈ t.post₁ s α }

-- Definition 2.3
def post₃ (c : Set t.S) (α : t.Act) : Set t.S := { s' | ∃ s ∈ c, s' ∈ t.post₁ s α }

-- Definition 2.3
def post₄ (c : Set t.S) : Set t.S := { s' | ∃ s ∈ c, s' ∈ t.post₂ s }

-- Definition 2.3
def pre₁ (s : t.S) (α : t.Act) : Set t.S := { s' | s' -[t, α]→ s }

-- Definition 2.3
def pre₂ (s : t.S) : Set t.S := { s' | ∃ α, s' ∈ t.pre₁ s α }

-- Definition 2.3
def pre₃ (c : Set t.S) (α : t.Act) : Set t.S := { s' | ∃ s ∈ c, s' ∈ t.pre₁ s α }

-- Definition 2.3
def pre₄ (c : Set t.S) : Set t.S := { s' | ∃ s ∈ c, s' ∈ t.pre₂ s }

-- Definition 2.4
def terminal (s : t.S) : Prop := t.post₂ s = ∅

-- Definition 2.5.1
structure actionDeterministic : Prop where
  init : t.I.subsingleton
  post : ∀ s α, (t.post₁ s α).subsingleton

-- Definition 2.5.2
structure apDeterministic : Prop where
  init : t.I.subsingleton
  post : ∀ s aps, (t.post₂ s ∩ { s' | t.L s' = aps }).subsingleton

-- Definition 2.6
structure ExecFragment where
  sₒ : t.S
  tail : Nat → Option (t.Act × t.S)
  tailSeq : ∀ i, tail i = none → tail (i + 1) = none
  wfHeadTrans : ∀ i₁ α₁ s₁, tail i₁ = some (α₁, s₁) → (sₒ -[t, α₁]→ s₁)
  wfTailTrans : ∀ i α₁ α₂ s₁ s₂, tail i = some (α₁, s₁) → tail (i + 1) = some (α₂, s₂) → (s₁ -[t, α₂]→ s₂)

namespace ExecFragment

-- An execution fragment consisting of only one state.
def singleton (s : t.S) : ExecFragment t := {
  sₒ := s,
  tail := λ _ => none,
  tailSeq := λ _ _ => rfl, 
  wfHeadTrans := λ _ _ _ h => by simp at h,
  wfTailTrans := λ _ _ _ _ _ h => by simp at h
}

variable {t}

-- Definition 2.6
def finite (f : ExecFragment t) : Prop := ∃ i, f.tail i = none

theorem singleton_finite (t) (s : t.S) : (singleton t s).finite := by
  simp only [singleton, finite]
  exact ⟨0, True.intro⟩

-- Definition 2.6
def infinite (f : ExecFragment t) : Prop := ∀ i, f.tail i ≠ none

theorem finite_or_infinite (f : ExecFragment t) : f.finite ∨ f.infinite := by
  sorry

theorem finite_has_end (f : ExecFragment t) (h : f.finite) : 
  ∃ i, f.tail i = none ∧ ∀ j, j < i → f.tail j ≠ none :=
  sorry

-- Definition 2.6
noncomputable def length (f : ExecFragment t) (h : f.finite) : Nat := (finite_has_end f h).choose

theorem pred_of_positive_length_ne_none (f : ExecFragment t) (hf : f.finite) (hl : 0 < f.length hf) : 
  f.tail (f.length hf - 1) ≠ none := by
    simp only [length] at *
    have hc := (finite_has_end f hf).choose_spec.right (finite_has_end f hf).choose -- hl
    sorry
    /-let x := (Option.ne_none_iff_exists (o := f.tail n)).mp (by
      simp only [length] at hm
      have hc := Exists.choose_spec (finite_has_end f h)
      rw [hm] at hc
      exact hc.right n (Nat.lt_succ_self n)
    )-/

-- TODO: Remove this.
lemma Nat.zero_lt_succ (n : Nat) : 0 < Nat.succ n := sorry

-- Gets the last state in a finite execution.
noncomputable def last (f : ExecFragment t) (h : f.finite) : t.S := 
  match hm:f.length h with
  | 0 => f.sₒ
  | n + 1 => 
    have hl : 0 < length f h := by simp [hm, Nat.zero_lt_succ]
    (Option.ne_none_iff_exists.mp $ pred_of_positive_length_ne_none f h hl).choose.snd

theorem singleton_last (t) (s : t.S) : (singleton t s).last (singleton_finite t s) = s := by
  simp only [last]
  sorry
  /-
  cases (singleton t s).length (singleton_finite t s)
  case zero => simp [singleton]
  case succ => sorry
  -/

-- Definition 2.7
inductive maximal (f : ExecFragment t) : Prop
  | finite (h : f.finite) : t.terminal (f.last h) → maximal f
  | infinite : f.infinite → maximal f

-- Definition 2.7
def initial (f : ExecFragment t) : Prop := f.sₒ ∈ t.I

end ExecFragment

-- Definition 2.9
structure Execution extends ExecFragment t where
  initial : toExecFragment.initial
  maximal : toExecFragment.maximal

-- Definition 2.10
def reachable (s : t.S) : Prop :=
  ∃ (f : ExecFragment t) (h : f.finite), f.initial ∧ (f.last h = s) 

-- Definition 2.10
def reach : Set t.S := { s | t.reachable s }

variable {S₁ S₂ Act AP₁ AP₂ : Type _}

-- Definition 2.42
def syncProd (t₁ t₂ : TransSys) : TransSys := {
  S := t₁.S × t₂.S,
  Act := t₁.Act × t₂.Act,
  trans := λ s₁ α s₂ => (s₁.1 -[t₁, α.1]→ s₂.1) ∧ (s₁.2 -[t₂, α.2]→ s₂.2),
  I := { i | i.1 ∈ t₁.I ∧ i.2 ∈ t₂.I }, 
  AP := t₁.AP ⊕ t₂.AP,
  L := λ (s₁, s₂) => ((t₁.L s₁).image Sum.inl) ∪ ((t₂.L s₂).image Sum.inr)
}  

-- Definition 2.42
notation t₁ " ⊗ " t₂ => TransSys.syncProd t₁ t₂

end TransSys