# Explanation

## The problem

In an effect system with explicit nesting, the programmer writes

```
handle (handle (handle body H1) H2) H3
```

and the trouble is that they already *know* the intent ("Auth must be inside
Cache") but must still translate it into an order, by hand, every time. Ordering
mistakes are silent: the program still runs, with different effect semantics.

## Why a static ordering is enough

An arrow imposes a **linear, sequential** structure on the operations of a
handler: there is no concurrent interleaving to account for. So the topology does
not need to be discovered at runtime — it can be decided once, at compile time,
as a linear extension of the declared precedence relation. That is the whole
proposal: the compiler computes the extension and folds it into the nested
`handle` term.

## What has to be true for that to be sound

The formalization is the argument that the shortcut is legitimate:

- **Precedence is a partial order.** A cycle in the declared relation has no
  linear extension, so it must be rejected rather than silently reordered —
  `cyclic_detection` is that case.
- **Any linear extension is a valid topology.** The topological-sort development
  (`ListDigraph/TopSort`, `Dts/TopoSort`) establishes that the extension respects
  every declared relation.
- **Nesting order determines semantics.** `Dts/Semantics` gives the meaning of a
  nested `handle`; `Dts/SemanticEquivalence` connects the synthesized term to it,
  so synthesis is not merely a rearrangement of syntax.
- **Unrelated handlers commute — sometimes.** `Dts/Commutativity` states when two
  handlers may be reordered, which is exactly the freedom the tie-break rule
  uses.

## Determinism is part of the contract

Unrelated handlers have no precedence constraint, so *some* order must be chosen.
The implementation uses declaration order as the tie-break, which makes the
synthesized term a function of the input text — two runs of the compiler on the
same source always emit the same nesting. Without that, the pass would be
correct but unreproducible.

## Why there is a Python implementation at all

A proof says the transformation is sound; it does not say the transformation is
implementable or pleasant. The reference pipeline (`dts.precedence_parser` plus
the case studies) keeps the formalization honest against concrete precedence
shapes — middleware stacks, event-driven orders, cyclic specs — and the property
suite turns the paper's claims into runnable checks.

See the [reference](/research-dts/reference/) for the modules and the
[how-to guides](/research-dts/how-to/) for build recipes.
