import Mathlib

open Classical

/- TEMP BEGIN -/
macro "obtain " t:term " := " h:term : tactic => 
  `(match $h:term with | $t:term => ?_)

@[simp] theorem Set.mem_set_of_eq {a : α} {p : α → Prop} : (a ∈ {a | p a}) = p a := sorry
theorem Set.ext_iff {s t : Set α} : s = t ↔ ∀ x, x ∈ s ↔ x ∈ t := sorry

def Trace (AP) := Nat → Set AP
def Trace.suffix {AP} (σ : Trace AP) (m : Nat) : Trace AP := λ n => σ (n + m)
notation:max σ:max "[" m "+]" => Trace.suffix σ m

@[simp]
theorem Trace.suffix_zero {AP} (σ : Trace AP) : σ[0+] = σ := by
  simp [suffix]

theorem Trace.suffix_split {AP} (σ : Trace AP) {m n : Nat} : σ[m+][n+] = σ[(m + n)+] := by
  sorry

theorem Trace.suffix_shuffle {AP} (σ : Trace AP) {m n : Nat} : σ[m+][n+] = σ[n+][m+] := by
  sorry

-- TODO: Macros for ∃∞ and ∀∞

/- TEMP END -/

-- Definition 5.1
inductive LTLFormula (AP) where
  | «true» : LTLFormula AP
  | atomic : AP → LTLFormula AP
  | not :    LTLFormula AP → LTLFormula AP
  | and :    LTLFormula AP → LTLFormula AP → LTLFormula AP
  | next :   LTLFormula AP → LTLFormula AP
  | until :  LTLFormula AP → LTLFormula AP → LTLFormula AP

variable {AP}

namespace LTLFormula

instance : Coe AP (LTLFormula AP) := ⟨LTLFormula.atomic⟩

notation "⊤" => LTLFormula.true
notation:max "¬" f:40 => LTLFormula.not f
notation:max "◯" f:40 => LTLFormula.next f
infixr:35 " ∧ " => LTLFormula.and
infixr:35 " U " => LTLFormula.until

def or (φ₁ φ₂ : LTLFormula AP) : LTLFormula AP := ¬(¬φ₁ ∧ ¬φ₂)
infixr:30 " ∨ " => or

def implication (φ₁ φ₂ : LTLFormula AP) : LTLFormula AP := ¬φ₁ ∨ φ₂
infixr:25 " → " => implication

def equivalence (φ₁ φ₂ : LTLFormula AP) : LTLFormula AP := (φ₁ → φ₂) ∧ (φ₂ → φ₁)
infixr:20 " ↔ " => equivalence

def eventually (φ : LTLFormula AP) : LTLFormula AP := ⊤ U φ
notation:max "◇" φ:40 => eventually φ

def always (φ : LTLFormula AP) : LTLFormula AP := ¬◇¬φ
notation:max "□" φ:40 => always φ

-- Definition 5.6
def satisfies {AP} (σ : Trace AP) : LTLFormula AP → Prop
  | ⊤         => True
  | (a : AP)  => a ∈ (σ 0)
  | not φ     => ¬(satisfies σ φ)
  | and φ₁ φ₂ => (satisfies σ φ₁) ∧ (satisfies σ φ₂)
  | ◯φ        => satisfies σ[1+] φ
  | φ₁ U φ₂   => ∃ j, (satisfies σ[j+] φ₂) ∧ ∀ i, i < j → (satisfies σ[i+] φ₁)

infix:15 " ⊨ " => satisfies

def words (φ : LTLFormula AP) := {σ | σ ⊨ φ}

variable {φ φ₁ φ₂ : LTLFormula AP} {σ : Trace AP}

theorem or_sat : (σ ⊨ φ₁ ∨ φ₂) ↔ (σ ⊨ φ₁) ∨ (σ ⊨ φ₂) := by
  simp [or, satisfies]
  constructor
  case mp =>
    intro h
    byCases hc : σ ⊨ φ₁
    case inl => exact Or.inl hc
    case inr => exact Or.inr (h hc)
  case mpr =>
    intro h h'
    exact h.resolve_left h'

theorem implication_sat : (σ ⊨ φ₁ → φ₂) ↔ (σ ⊨ φ₁) → (σ ⊨ φ₂) := by
  simp [satisfies]

theorem equivalence_sat : (σ ⊨ φ₁ ↔ φ₂) ↔ ((σ ⊨ φ₁) ↔ (σ ⊨ φ₂)) := by
  simp [equivalence]
  constructor
  case mp =>
    intro h
    simp [satisfies] at h
    exact ⟨h.left, h.right⟩
  case mpr =>
    intro h
    simp [satisfies]
    exact ⟨h.mp, h.mpr⟩

theorem eventually_sat : (σ ⊨ ◇φ) ↔ (∃ j, σ[j+] ⊨ φ) := by
  simp [satisfies]

theorem always_sat : (σ ⊨ □φ) ↔ (∀ j, σ[j+] ⊨ φ) := by
  simp [satisfies]

-- Definition 5.17
def equivalent (φ₁ φ₂ : LTLFormula AP) : Prop := 
  φ₁.words = φ₂.words

infix:15 " ≡ " => equivalent

theorem equivalent_ext : (φ₁ ≡ φ₂) ↔ ∀ σ, (σ ⊨ φ₂) ↔ (σ ⊨ φ₁) := by
  constructor <;> (
    simp [equivalent, Set.ext_iff, words, Set.mem_set_of_eq]
    intro h σ
    exact Iff.symm $ h σ
  )

@[simp]
theorem equivalent_refl : φ ≡ φ := by
  simp [equivalent]

@[simp]
theorem equivalent_from_eq : (φ₁ = φ₂) → (φ₁ ≡ φ₂) :=
  λ h => by simp [h]

@[simp]
theorem equivalent_trans : (φ ≡ φ₁) → (φ₁ ≡ φ₂) → (φ ≡ φ₂) := by
  simp [equivalent]
  exact Eq.trans

-- Subsitute ψ₁ with ψ₂ in φ.
noncomputable def substitute (φ ψ₁ ψ₂ : LTLFormula AP) : LTLFormula AP :=
  if φ = ψ₁ then ψ₂ else
  match φ with
  | ⊤           => ⊤
  | (a : AP)    => a
  | not φ'      => ¬(substitute φ' ψ₁ ψ₂)
  | and φ'₁ φ'₂ => (substitute φ'₁ ψ₁ ψ₂) ∧ (substitute φ'₂ ψ₁ ψ₂)
  | ◯φ'         => ◯(substitute φ' ψ₁ ψ₂)
  | φ'₁ U φ'₂   => (substitute φ'₁ ψ₁ ψ₂) U (substitute φ'₂ ψ₁ ψ₂)

theorem substitute_equiv (h : φ₁ ≡ φ₂) : φ ≡ φ.substitute φ₁ φ₂ := by
  induction φ 
  case true => 
    simp only [substitute]
    split
    case inl h' => simp [h', h]
    case inr => simp
  case atomic => 
    simp only [substitute]
    split
    case inl h' => simp [h', h]
    case inr => simp
  case not φ' hi =>
    simp only [substitute]
    split 
    case inl h' => simp [h', h] 
    case inr =>
      simp [equivalent_ext] at hi ⊢
      intro σ
      simp only [satisfies]
      exact ⟨mt (hi σ).mpr, mt (hi σ).mp⟩
  case and φ'₁ φ'₂ hi₁ hi₂ =>
    simp only [substitute]
    split
    case inl h' => simp [h', h] 
    case inr =>
      simp [equivalent_ext] at hi₁ hi₂ ⊢
      intro σ
      simp only [satisfies]
      constructor
      case mp =>
        intro h
        exact ⟨(hi₁ σ).mp h.left, (hi₂ σ).mp h.right⟩
      case mpr =>
        intro h
        exact ⟨(hi₁ σ).mpr h.left, (hi₂ σ).mpr h.right⟩
  case next φ' hi =>
    simp only [substitute]
    split 
    case inl h' => simp [h', h] 
    case inr =>
      simp [equivalent_ext] at hi ⊢
      intro σ
      simp only [satisfies]
      exact hi σ[1+]
  case until φ'₁ φ'₂ hi₁ hi₂ =>
    simp only [substitute]
    split
    case inl h' => simp [h', h] 
    case inr =>
      simp [equivalent_ext] at hi₁ hi₂ ⊢
      intro σ
      simp only [satisfies]
      constructor
      case mp =>
        intro ⟨j, hj, hij⟩
        exists j
        apply And.intro $ (hi₂ σ[j+]).mp hj
        intro i hi
        exact (hi₁ σ[i+]).mp (hij i hi)
      case mpr =>
        intro ⟨j, hj, hij⟩
        exists j
        apply And.intro $ (hi₂ σ[j+]).mpr hj
        intro i hi
        exact (hi₁ σ[i+]).mpr (hij i hi)

@[simp]
theorem double_negation : ¬¬φ ≡ φ := by
  rw [equivalent_ext]
  intro σ
  simp [satisfies]

@[simp]
theorem next_duality : ¬◯φ ≡ ◯¬φ := by
  rw [equivalent_ext]
  intro σ
  constructor <;> (intro h; exact h)

@[simp]
theorem eventually_duality : ¬◇φ ≡ □¬φ := by
  rw [equivalent_ext]
  intro σ
  constructor <;> (
    intro h
    simp [satisfies] at *
    exact h
  )

@[simp]  
theorem always_duality : ¬□φ ≡ ◇¬φ := by
  rw [equivalent_ext]
  intro σ
  constructor <;> (
    intro h
    simp [satisfies] at *
    exact h
  )

@[simp]
theorem eventually_idem : ◇◇φ ≡ ◇φ := by
  rw [equivalent_ext]
  intro σ
  simp [eventually]
  constructor
  case mp =>
    intro ⟨j, h⟩
    simp [satisfies] at *
    exact ⟨j, 0, h⟩
  case mpr =>
    simp [satisfies]
    intro j j' h
    simp [Trace.suffix_split] at h
    exact ⟨j + j', h⟩

@[simp]
theorem always_idem : □□φ ≡ □φ := by
  rw [equivalent_ext]
  intro σ
  simp [always]
  constructor
  case mp =>
    simp [satisfies]
    intro h j j'
    simp [Trace.suffix_split, h (j + j')] 
  case mpr =>
    simp [satisfies]
    intro h j
    exact h j 0

@[simp]
theorem until_idem_left : φ₁ U (φ₁ U φ₂) ≡ φ₁ U φ₂ := by
  rw [equivalent_ext]
  intro σ
  constructor
  case mp =>
    simp [satisfies]
    intro j h₁ h₂
    exists j
    constructor
    case left =>
      exists (0 : Nat)
      apply And.intro h₁
      intro i hi
      contradiction
    case right =>
      exact h₂
  case mpr =>
    intro h
    simp [satisfies] at h ⊢ 
    obtain ⟨j, ⟨⟨j', ⟨h₁, h₂⟩⟩, h₃⟩⟩ := h
    clear h
    exists j + j'
    simp [Trace.suffix_split] at h₁
    apply And.intro h₁
    clear h₁
    intro i hi
    have h₂':= h₂ i
    have h₃' := h₃ i
    clear h₂ h₃
    sorry -- unprovable from here

@[simp]
theorem until_idem_right : (φ₁ U φ₂) U φ₂ ≡ φ₁ U φ₂ := by
  sorry

set_option maxHeartbeats 100000

@[simp]
theorem eventually_absorption : ◇□◇φ ≡ □◇φ := by
  rw [equivalent_ext]
  intro σ
  constructor
  case mp =>
    intro h
    simp [satisfies] at h ⊢
    exists (0 : Nat)
    simp [h]
  case mpr =>
    intro h
    simp [satisfies] at *
    intro x
    obtain ⟨j, h⟩ := h
    obtain ⟨j', h⟩ := h x
    exists (j + j')
    simp [Trace.suffix_shuffle σ, Trace.suffix_split σ[x+]] at h
    exact h

end LTLFormula 







