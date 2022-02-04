import ModelChecking.Chapter2

variable (t : TransSys)

-- Definition 3.3
structure StateGraph where
  E : Set (t.S × t.S)
  wfE : ∀ e ∈ E, e.2 ∈ t.post₂ e.1

namespace StateGraph

variable {t} (g : StateGraph t)

-- Definition 3.3
abbrev V (g : StateGraph t) := t.S

-- Definition 3.3
inductive reachable : g.V → g.V → Prop
  | rfl (s) : reachable s s
  | edge (s₁ s₂) : (s₁, s₂) ∈ g.E → reachable s₁ s₂
  | trans (s₁ s₂ s₃) : reachable s₁ s₂ → reachable s₂ s₃ → reachable s₁ s₃

-- Definition 3.3
def post₁ (s : g.V) : Set g.V := { s' | g.reachable s s' }

-- Definition 3.3
def post₂ (c : Set g.V) : Set g.V := { s' | ∃ s ∈ c, s' ∈ g.post₁ s }

-- Definition 3.3
def pre₁ (s : g.V) : Set g.V := { s' | g.reachable s' s }

-- Definition 3.3
def pre₂ (c : Set g.V) : Set g.V := { s' | ∃ s ∈ c, s' ∈ g.pre₁ s }

-- Page 95
theorem reach_of_ts_eq_post₂_I : t.reach = g.post₂ t.I := by
  simp only [TransSys.reach, TransSys.reachable, post₂, post₁]
  ext s
  apply Iff.intro
  case h.a.mp =>
    sorry
  case h.a.mpr =>
    intro h
    obtain ⟨v, ⟨hv, hs⟩⟩ := h
    have hs := Set.mem_set_of_eq.mp hs
    apply Set.mem_set_of_eq.mpr
    cases hs
    case rfl =>
      exists TransSys.ExecFragment.singleton t s
      exists TransSys.ExecFragment.singleton_finite t s
      exact ⟨hv, TransSys.ExecFragment.singleton_last t s⟩
    case edge => sorry 
    case trans => sorry



end StateGraph
