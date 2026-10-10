module
public import Aeneas.Std.Scalar.Core
public meta import Lean.Elab.Tactic.Basic
public meta import Lean.Meta.Tactic.Revert
public meta import Lean.Meta.Tactic.Intro
public meta import Lean.Meta.Tactic.Replace
public meta import Lean.Meta.Transform
public meta import Lean.Meta.LitValues
public section

/-!
# `bv_lit_widths`: make the bit-widths of scalar bit-vectors literal

Since Lean v4.34, `bv_decide` reads bit-widths *syntactically*: the width of a
`BitVec w` term is only understood if `w` is a numeral (`OfNat.ofNat (nat_lit n)`), see
`Lean.Meta.Sym.getNatValue?`. Before, it used `Lean.Meta.getNatValue?`, which reduces `w`.

The bit-vector of a machine integer is `x.bv : BitVec ty.numBits`, so after `bvify` a goal
mentions widths such as `UScalarTy.numBits .U32` (both in the type arguments of the
bit-vector operations and, crucially, in the *inferred* type of every atom `x.bv`).
`bv_decide` then abstracts every expression containing such a term as an opaque variable
and reports spurious counterexamples.

`bvLitWidths` rewrites a goal, *definitionally*, into one where every such width is a literal:
1. All the propositional hypotheses are reverted into the goal.
2. Every occurrence of `UScalarTy.numBits ty`, `IScalarTy.numBits ty` (for a concrete,
   fixed-size `ty`) and `U8.numBits`, ..., `I128.numBits` is replaced with the numeral it
   reduces to. The result is definitionally equal to the original goal.
3. Every atom `x.bv` (`UScalar.bv`/`IScalar.bv`, whose inferred type is
   `BitVec ty.numBits`, and the `abbrev`s `U32.bv : U32 → BitVec 32` & co., which
   `bv_decide` unfolds back to `UScalar.bv` during its preprocessing) is generalized to a
   fresh variable of type `BitVec n`, `n` a literal.
   The original goal is closed by applying the new goal to the atoms; the kernel checks that
   `BitVec ty.numBits` and `BitVec n` agree.
4. The hypotheses are re-introduced, with their original names.

Since `bv_decide` treats `x.bv` as an uninterpreted atom anyway, step 3 does not lose any
information it could use. `Usize`/`Isize` are left untouched: their width
`System.Platform.numBits` is not a numeral, and `bv_decide` cannot reason about them.
-/

namespace Aeneas.BvLitWidths

open Lean Meta Elab Tactic
open Aeneas.Std

/-- The bit-width constants of the fixed-size scalar types. -/
meta def widthConsts : Std.HashSet Name := Std.HashSet.ofList [
  ``U8.numBits, ``U16.numBits, ``U32.numBits, ``U64.numBits, ``U128.numBits,
  ``I8.numBits, ``I16.numBits, ``I32.numBits, ``I64.numBits, ``I128.numBits
]

/-- If `e` is the bit-width of a concrete scalar type and it reduces to a numeral `n`,
return `n`. -/
meta def evalWidth? (e : Expr) : MetaM (Option Nat) := do
  let isWidth :=
    ((e.isAppOfArity ``UScalarTy.numBits 1 || e.isAppOfArity ``IScalarTy.numBits 1) &&
      !e.appArg!.hasLooseBVars && !e.appArg!.hasFVar && !e.appArg!.hasMVar) ||
    (e.isConst && widthConsts.contains e.constName!)
  if !isWidth then return none
  -- `U32.numBits` & co. are `irreducible_def`s: we need `.all` to unfold them
  let r ← withTransparency .all <| whnf e
  match r with
  | .lit (.natVal n) => return some n
  | _ => getNatValue? r

/-- Replace every scalar bit-width in `e` that reduces to a numeral by that numeral.
The result is definitionally equal to `e`. -/
meta def normWidths (e : Expr) : MetaM Expr :=
  Meta.transform e (pre := fun e => do
    if let some n ← evalWidth? e then return .done (mkNatLit n)
    return .continue)

/-- The `abbrev`s `U32.bv : U32 → BitVec 32` & co. Their result type is a literal, but
`bv_decide` unfolds reducible definitions while preprocessing, so `x.bv` becomes
`UScalar.bv x : BitVec (UScalarTy.numBits .U32)` again: we must generalize them too. -/
meta def fixedBvFns : Std.HashSet Name := Std.HashSet.ofList [
  ``U8.bv, ``U16.bv, ``U32.bv, ``U64.bv, ``U128.bv,
  ``I8.bv, ``I16.bv, ``I32.bv, ``I64.bv, ``I128.bv
]

/-- If `e` is a scalar bit-vector `x.bv` (`UScalar.bv`, `IScalar.bv`, the corresponding
projections, or `U32.bv` & co.) of a fixed-size scalar type, return its width. -/
meta def atomWidth? (e : Expr) : MetaM (Option Nat) := do
  if e.hasLooseBVars then return none
  let isScalarBv :=
    e.isAppOfArity ``UScalar.bv 2 || e.isAppOfArity ``IScalar.bv 2 ||
    (e.getAppNumArgs == 1 && e.getAppFn.isConst && fixedBvFns.contains e.getAppFn.constName!) ||
    (match e with
     | .proj n 0 _ => n == ``UScalar || n == ``IScalar
     | _ => false)
  if !isScalarBv then return none
  let ty ← instantiateMVars (← inferType e)
  let_expr BitVec w := ty | return none
  if let some n ← getNatValue? w then return some n
  evalWidth? w

/-- Collect the scalar bit-vector atoms of `e`, outermost first, without duplicates. -/
meta partial def collectAtoms (e : Expr) : StateT (Array (Expr × Nat)) MetaM Unit := do
  if let some n ← atomWidth? e then
    unless (← get).any (·.1 == e) do modify (·.push (e, n))
    return
  match e with
  | .app f a => collectAtoms f; collectAtoms a
  | .lam _ t b _ | .forallE _ t b _ => collectAtoms t; collectAtoms b
  | .letE _ t v b _ => collectAtoms t; collectAtoms v; collectAtoms b
  | .mdata _ b | .proj _ _ b => collectAtoms b
  | _ => pure ()

/-- A readable name for the variable generalizing atom `a` (`x.bv` ↦ `x_bv`). -/
meta def atomName (a : Expr) : MetaM Name := do
  let x := match a with
    | .proj _ _ x => x
    | _ => a.appArg!
  if x.isFVar then
    return (← x.fvarId!.getUserName).appendAfter "_bv"
  else
    return `bv

/-- See the module documentation. Returns the new goal. -/
meta def bvLitWidths (g : MVarId) : MetaM MVarId := g.withContext do
  g.checkNotAssigned `bv_lit_widths
  -- 1. Revert the propositional hypotheses (and whatever depends on them)
  let mut props := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    if ← isProp d.type then props := props.push d.fvarId
  let (reverted, g) ← g.revert props (preserveOrder := true)
  g.withContext do
  -- 2. Normalize the widths
  let tgt ← normWidths (← instantiateMVars (← g.getType))
  -- 3. Generalize the atoms
  let ((), atoms) ← (collectAtoms tgt).run #[]
  let decls ← atoms.mapM fun (a, n) => do
    return (← atomName a, fun (_ : Array Expr) =>
      pure (mkApp (mkConst ``BitVec) (mkNatLit n)))
  let newTgt ← withLocalDeclsD decls fun ys => do
    let body := tgt.replace fun e =>
      match atoms.findIdx? (·.1 == e) with
      | some i => some ys[i]!
      | none => none
    mkForallFVars ys body
  let g' ← mkFreshExprSyntheticOpaqueMVar newTgt (← g.getTag)
  g.assign (mkAppN g' (atoms.map (·.1)))
  -- 4. Re-introduce everything
  let (_, g) ← g'.mvarId!.introNP (atoms.size + reverted.size)
  -- Also normalize the types of the remaining (non propositional) bit-vector variables
  g.withContext do
  let mut g := g
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if ty.isAppOfArity ``BitVec 1 then
      let ty' ← normWidths ty
      if ty' != ty then g ← g.replaceLocalDeclDefEq d.fvarId ty'
  return g

/-- `bv_lit_widths` rewrites the goal (definitionally) so that the bit-width of every
machine-integer bit-vector `x.bv` is a numeral, which `bv_decide` requires since Lean v4.34.
The atoms `x.bv` are generalized to fresh variables `x_bv : BitVec n`.

Typical use: `bvify 32 at *; bv_lit_widths; bv_decide` (`bv_tac` does this automatically). -/
syntax (name := bvLitWidthsTac) "bv_lit_widths" : tactic

@[tactic bvLitWidthsTac]
meta def evalBvLitWidths : Tactic := fun _ =>
  liftMetaTactic fun g => return [← bvLitWidths g]

end Aeneas.BvLitWidths
