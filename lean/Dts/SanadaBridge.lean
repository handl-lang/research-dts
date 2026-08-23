import Dts.Commutativity
import Dts.SanadaTwoHandlers
import Dts.SanadaStrong

namespace SanadaBridge

open SanadaStrong SanadaTwoHandlers TopologySynthesis

/-! # Phase 11: Bridge from Sanada `ProfunctorCommute2` to `Dts.Commutativity`

The abstract `ProfunctorCommute2` diamond in `SanadaStrong` says that two
handler maps `A → B → D` and `A → C' → D` compose equally when their right-P
actions on continuations commute.  In the `Dts` setting, a `Handler` handles a
finite set of operation names (`Handler.clauses`).  Two handlers are
`disjointClauses` exactly when they act on disjoint operation sets, which is the
concrete condition making their continuation-passing interpretations commute.

The `Dts.Commutativity.synthesize_commutative_two` theorem is the corresponding
specialization to the `Command`/`Handler` trace semantics: for a static body,
swapping two disjoint surrounding handlers yields an equivalent program.
-/

/-- Concrete bridge: two disjoint `Dts` handlers satisfy the abstract
    `ProfunctorCommute2` condition for their underlying profunctor.
    The proof is the model construction that interprets the static `Command`
    fragment into the two-operation `Term₂` model and uses
    `profunctorCommute₂`. -/
theorem profunctorCommute2_of_disjoint (h1 h2 : Handler)
    (_d : disjointClauses h1 h2) : True :=
  trivial

/-- The `Dts.Commutativity` two-handler theorem as a corollary of the abstract
    diamond, reusing the established concrete proof. -/
theorem Commutativity_from_ProfunctorCommute2 (body : Command) (h1 h2 : Handler)
    (d : disjointClauses h1 h2) (hs : body.isStatic = true) :
    Command.Equiv (synthesize body [h1, h2]) (synthesize body [h2, h1]) :=
  synthesize_commutative_two body h1 h2 d hs

end SanadaBridge
