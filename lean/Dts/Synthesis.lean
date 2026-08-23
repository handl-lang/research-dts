import Mathlib.Tactic
import Dts.Basic
import Dts.Precedence
import ListDigraph.Basic

namespace TopologySynthesis

open ListDigraph

-- Section 4: Synthesis

/-- `synthesize body ordered` folds `handle` over the ordered handler list,
    producing a linearly nested term. Corresponds to `S(D, P)` in the paper
    where `ordered` is the linear extension computed from `D = (H, ≺)`. -/
def synthesize (body : Command) (ordered : List Handler) : Command :=
  ordered.foldl (fun acc h => Command.handle acc h) body

-- Section 6: Proofs

-- Proposition 1: Well-Formedness

/-- Wrapping with a handler preserves well-formedness if the handler
    has at least one clause. -/
theorem handle_preserves_well_formed
    (body : Command) (h : Handler)
    (hwf : body.isWellFormed = true)
    (hclauses : h.clauses.length > 0) :
    (Command.handle body h).isWellFormed = true := by
  simp [Command.isWellFormed, hwf, hclauses]

/-- **Proposition 1**: Synthesis preserves well-formedness if every
    handler in the ordered list has at least one clause. -/
theorem synthesize_well_formed
    (body : Command) (ordered : List Handler)
    (hwf : body.isWellFormed = true)
    (hclauses : ∀ h ∈ ordered, h.clauses.length > 0) :
    (synthesize body ordered).isWellFormed = true := by
  unfold synthesize
  induction ordered generalizing body with
  | nil => exact hwf
  | cons h t ih =>
    simp only [List.foldl_cons]
    have h_clause : h.clauses.length > 0 := hclauses h (by simp)
    have h_wf : (Command.handle body h).isWellFormed = true :=
      handle_preserves_well_formed _ _ hwf h_clause
    have h_clauses_t : ∀ h' ∈ t, h'.clauses.length > 0 := by
      intro h' h'_in
      exact hclauses h' (List.mem_cons_of_mem _ h'_in)
    exact ih _ h_wf h_clauses_t

-- Proposition 2: Precedence Preservation

inductive NestedInside : Command → Handler → Handler → Prop where
  | direct (body : Command) (inner outer : Handler) :
    NestedInside (Command.handle (Command.handle body inner) outer) inner outer
  | wrap_new (body : Command) (mid inner outer : Handler)
    (h : NestedInside body inner mid) :
    NestedInside (Command.handle body outer) inner outer
  | wrap_keep (body : Command) (inner mid outer : Handler)
    (h : NestedInside body inner mid) :
    NestedInside (Command.handle body outer) inner mid


/-- Folding `rest` outside `cmd` preserves an existing nesting of
    `inner` inside `outer`. The target `outer` is NOT in the fold list. -/
theorem nesting_preserved_through_foldl
    (cmd : Command) (inner outer : Handler) (rest : List Handler)
    (h : NestedInside cmd inner outer) :
    NestedInside (synthesize cmd rest) inner outer := by
  unfold synthesize
  induction rest generalizing cmd with
  | nil => exact h
  | cons h' t' ih =>
    simp only [List.foldl_cons]
    exact ih _ (NestedInside.wrap_keep _ _ outer h' h)

/-- Folding `rest` outside `cmd` establishes nesting between `inner` and
    every handler in `rest`, given that `inner` is already nested inside
    some `mid` in `cmd`. -/
theorem nesting_preserved_by_foldl
    (cmd : Command) (inner mid : Handler) (rest : List Handler)
    (h : NestedInside cmd inner mid) :
    ∀ r ∈ rest, NestedInside (synthesize cmd rest) inner r := by
  intro r
  induction rest generalizing cmd with
  | nil => intro r_in; simp at r_in
  | cons h' t' ih =>
    intro r_in
    simp only [synthesize, List.foldl_cons]
    by_cases heq : r = h'
    · -- r = h': establish inner inside r via wrap_new, then preserve through t'
      subst heq
      exact nesting_preserved_through_foldl _ _ _ t'
        (NestedInside.wrap_new _ mid _ r h)
    · -- r in t': preserve nesting through wrap_keep, then apply IH
      have r_in_t' : r ∈ t' := by
        simp at r_in; cases r_in
        case inl h_eq => exact absurd h_eq heq
        case inr h => exact h
      exact ih _ (NestedInside.wrap_keep _ _ mid h' h) r_in_t'

/-- **Proposition 2**: if `hi` appears before `hj` in the ordered list,
    then `hi` is nested inside `hj` in the synthesized term. -/
theorem synthesize_preserves_precedence
    (ordered : List Handler) (hi hj : Handler)
    (h_before : AppearsBefore hi hj ordered) :
    ∀ body, NestedInside (synthesize body ordered) hi hj := by
  induction h_before with
  | head rest hj_in_rest =>
    intro body
    simp only [synthesize, List.foldl_cons]
    cases rest with
    | nil => simp at hj_in_rest
    | cons h' rest' =>
      simp only [List.foldl_cons]
      by_cases heq : hj = h'
      · -- hj = h': hi is head, hj is second handler — direct nesting
        subst heq
        exact nesting_preserved_through_foldl _ _ _ rest'
          (NestedInside.direct _ _ _)
      · -- hj in rest': hi is head, h' is second, hj is deeper
        have hj_in_rest' : hj ∈ rest' := by
          simp at hj_in_rest; cases hj_in_rest
          case inl h => exact absurd h heq
          case inr h => exact h
        exact nesting_preserved_by_foldl
          (Command.handle (Command.handle body hi) h') hi h' rest'
          (NestedInside.direct _ _ _) hj hj_in_rest'
  | tail h rest h_ab ih =>
    intro body
    simp only [synthesize, List.foldl_cons]
    exact ih (Command.handle body h)

-- Proposition 3: Static Topology

/-- Wrapping with a handler preserves staticity. -/
theorem handle_preserves_static
    (body : Command) (h : Handler)
    (hs : body.isStatic = true) :
    (Command.handle body h).isStatic = true := by
  simp [Command.isStatic, hs]

/-- **Proposition 3**: Synthesis preserves staticity — if the body is
    static (contains no `cond`), wrapping with handlers never introduces
    runtime branching. -/
theorem synthesize_static_topology
    (body : Command) (ordered : List Handler)
    (hs : body.isStatic = true) :
    (synthesize body ordered).isStatic = true := by
  unfold synthesize
  induction ordered generalizing body with
  | nil => simp [List.foldl_nil]; exact hs
  | cons h t ih =>
    simp only [List.foldl_cons]
    have h_static : (Command.handle body h).isStatic = true :=
      handle_preserves_static _ _ hs
    exact ih _ h_static

-- Completeness: linear extension realizes all precedence constraints

/-- **Corollary (Completeness)**: If `ordered` is a linear extension of
    `prec` (every precedence constraint `prec a b` implies `a` appears
    before `b` in the list), then synthesis realizes every precedence
    constraint as handler nesting.

    The existence of such a list for any finite acyclic precedence
    relation is proven in `TopoSort.lean` as `exists_linear_extension`.
    What this theorem establishes is that *given* such a list, the
    synthesis function correctly realizes all constraints. -/
theorem synthesize_completeness
    (ordered : List Handler) (prec : Precedence)
    (hi hj : Handler)
    (h_prec : prec hi hj = true)
    (h_linext : ∀ a b : Handler, prec a b = true → AppearsBefore a b ordered) :
    ∀ body, NestedInside (synthesize body ordered) hi hj := by
  exact synthesize_preserves_precedence ordered hi hj (h_linext hi hj h_prec)

end TopologySynthesis
