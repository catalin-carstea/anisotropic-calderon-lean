import Calderon.ActualReferenceTwoAngleNativeWeakHalfLiftCore
import Calderon.ActualReferenceTwoAngleWeakOperatorTopology
import Calderon.NativeParameterWeakLiftTopology

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

open SphereHarmonic NativeHarmonicH1LiftCompletion
attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
section NativeWeakHalfCanonicalInputs
attribute [local instance] weakHeaderDualZeroGroup weakHeaderDualZeroSpace

private lemma clm_normedAddCommGroup_constructor_heq
    {K L E E' F F' : Type}
    [rK : NontriviallyNormedField K] [rL : NontriviallyNormedField L]
    (gE : NormedAddCommGroup E) (gE' : NormedAddCommGroup E')
    (gF : NormedAddCommGroup F) (gF' : NormedAddCommGroup F')
    (sE : @NormedSpace K E rK.toNormedField gE.toSeminormedAddCommGroup)
    (sE' : @NormedSpace K E' rK.toNormedField gE'.toSeminormedAddCommGroup)
    (sF : @NormedSpace L F rL.toNormedField gF.toSeminormedAddCommGroup)
    (sF' : @NormedSpace L F' rL.toNormedField gF'.toSeminormedAddCommGroup)
    (σ : K →+* L) (i j : RingHomIsometric σ)
    (eE : E = E') (eF : F = F')
    (hgE : HEq gE gE') (hgF : HEq gF gF')
    (hsE : HEq sE sE') (hsF : HEq sF sF') :
    HEq
      (letI := gE; letI := gF; letI := sE; letI := sF; letI := i
       ContinuousLinearMap.toNormedAddCommGroup (E := E) (F := F) (σ₁₂ := σ))
      (letI := gE'; letI := gF'; letI := sE'; letI := sF'; letI := j
       ContinuousLinearMap.toNormedAddCommGroup (E := E') (F := F') (σ₁₂ := σ)) := by
  subst E'
  subst F'
  have he : gE = gE' := eq_of_heq hgE
  cases he
  have hf : gF = gF' := eq_of_heq hgF
  cases hf
  have hse : sE = sE' := eq_of_heq hsE
  cases hse
  have hsf : sF = sF' := eq_of_heq hsF
  cases hsf
  rfl

private lemma contDiff_referenceTwoAngleWeakDirichletEnergyFamily_nativeCanonical
    (hcalc : FixedSobolevCalculus) (i j k l : Fin 3) :
    ContDiff (E := ℝ × (ℝ × (ℝ × (R3 × ℝ))))
      (F := BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero) ℝ ∞
      (referenceTwoAngleWeakDirichletEnergyFamily
        g L y0 Φ B ε C ρ H a w hData hcalc i j k l) := by
  have hA := contDiff_referenceTwoAngleWeakDirichletEnergyFamily
    g L y0 Φ B ε C ρ H a w hData hcalc i j k l
  run_tac
    let goal ← Lean.Elab.Tactic.getMainGoal
    goal.withContext do
      let ctx ← Lean.getLCtx
      let some hd := ctx.findFromUserName? `hA | throwError "hA missing"
      let source := (← Lean.instantiateMVars hd.type).consumeMData
      let target := (← Lean.instantiateMVars (← goal.getType)).consumeMData
      let sa := source.getAppArgs
      let ta := target.getAppArgs
      unless sa.size == 10 && ta.size == 10 do
        throwError "Expected exact ten-argument ContDiff applications"
      let he ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkEq sa[5]! ta[5]!)
      let hg ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkHEq sa[6]! ta[6]!)
      let hf ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkHEq sa[9]! ta[9]!)
      let ci ← Lean.getConstInfo ``contDiff_real_carrier_transport
      let c := Lean.mkConst ``contDiff_real_carrier_transport
        (ci.levelParams.map (fun _ => Lean.Level.zero))
      goal.assign (Lean.mkAppN c #[ta[2]!, sa[5]!, ta[5]!, ta[3]!, ta[4]!,
        sa[6]!, ta[6]!, sa[7]!, ta[7]!, he, hg, sa[9]!, ta[9]!, hf,
        Lean.mkFVar hd.fvarId])
      Lean.Elab.Tactic.replaceMainGoal [he.mvarId!, hg.mvarId!, hf.mvarId!]
  ·
    rfl
  ·
    run_tac
      let goal ← Lean.Elab.Tactic.getMainGoal
      goal.withContext do
        let target := (← Lean.instantiateMVars (← goal.getType)).consumeMData
        let a := target.getAppArgs
        unless target.getAppFn.isConstOf ``HEq && a.size == 4 do
          throwError "Expected normed-group HEq"
        let mut lhs := a[1]!.consumeMData
        let mut rhs := a[3]!.consumeMData
        -- Unfold only a direct group alias, never a space or operator norm.
        for name in #[``weakHeaderSelfDualGroup, ``weakHeaderH1DualZeroGroup, ``weakHeaderDualZeroH1ZeroGroup] do
          if lhs.getAppFn.isConstOf name then
            let ci ← Lean.getConstInfo name
            let some body := ci.value? | throwError "Simple group body unavailable"
            lhs := body.consumeMData
          if rhs.getAppFn.isConstOf name then
            let ci ← Lean.getConstInfo name
            let some body := ci.value? | throwError "Simple group body unavailable"
            rhs := body.consumeMData
        let la := lhs.getAppArgs
        let ra := rhs.getAppArgs
        unless lhs.getAppFn.isConstOf ``ContinuousLinearMap.toNormedAddCommGroup &&
            rhs.getAppFn.isConstOf ``ContinuousLinearMap.toNormedAddCommGroup &&
            la.size == 12 && ra.size == 12 do
          throwError "Expected exact twelve-argument normed CLM constructors"
        for n in (#[0,1,6,7,10] : Array Nat) do
          unless la[n]! == ra[n]! do
            throwError "Fixed scalar constructor data changed at {n}"
        let eE ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkEq la[2]! ra[2]!)
        let eF ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkEq la[3]! ra[3]!)
        let hgE ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkHEq la[4]! ra[4]!)
        let hgF ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkHEq la[5]! ra[5]!)
        let hsE ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkHEq la[8]! ra[8]!)
        let hsF ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkHEq la[9]! ra[9]!)
        let ci ← Lean.getConstInfo ``clm_normedAddCommGroup_constructor_heq
        let c := Lean.mkConst ``clm_normedAddCommGroup_constructor_heq
          (ci.levelParams.map (fun _ => Lean.Level.zero))
        goal.assign (Lean.mkAppN c #[la[0]!, la[1]!, la[2]!, ra[2]!, la[3]!, ra[3]!,
          la[6]!, la[7]!, la[4]!, ra[4]!, la[5]!, ra[5]!,
          la[8]!, ra[8]!, la[9]!, ra[9]!, la[10]!, la[11]!, ra[11]!,
          eE, eF, hgE, hgF, hsE, hsF])
        Lean.Elab.Tactic.replaceMainGoal
          [eE.mvarId!, eF.mvarId!, hgE.mvarId!, hgF.mvarId!, hsE.mvarId!, hsF.mvarId!]
    ·
      rfl
    ·
      rfl
    ·
      rfl
    ·
      rfl
    ·
      rfl
    ·
      rfl
  ·
    rfl

private lemma contDiff_referenceTwoAngleWeakEnergyFamily_nativeCanonical
    (hcalc : FixedSobolevCalculus) (i j k l : Fin 3) :
    ContDiff (E := ℝ × (ℝ × (ℝ × (R3 × ℝ))))
      (F := BallH1 →L[ℝ] StrongDual ℝ BallH1Zero) ℝ ∞
      (referenceTwoAngleWeakEnergyFamily
        g L y0 Φ B ε C ρ H a w hData hcalc i j k l) := by
  have hA := contDiff_referenceTwoAngleWeakEnergyFamily
    g L y0 Φ B ε C ρ H a w hData hcalc i j k l
  run_tac
    let goal ← Lean.Elab.Tactic.getMainGoal
    goal.withContext do
      let ctx ← Lean.getLCtx
      let some hd := ctx.findFromUserName? `hA | throwError "hA missing"
      let source := (← Lean.instantiateMVars hd.type).consumeMData
      let target := (← Lean.instantiateMVars (← goal.getType)).consumeMData
      let sa := source.getAppArgs
      let ta := target.getAppArgs
      unless sa.size == 10 && ta.size == 10 do
        throwError "Expected exact ten-argument ContDiff applications"
      let he ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkEq sa[5]! ta[5]!)
      let hg ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkHEq sa[6]! ta[6]!)
      let hf ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkHEq sa[9]! ta[9]!)
      let ci ← Lean.getConstInfo ``contDiff_real_carrier_transport
      let c := Lean.mkConst ``contDiff_real_carrier_transport
        (ci.levelParams.map (fun _ => Lean.Level.zero))
      goal.assign (Lean.mkAppN c #[ta[2]!, sa[5]!, ta[5]!, ta[3]!, ta[4]!,
        sa[6]!, ta[6]!, sa[7]!, ta[7]!, he, hg, sa[9]!, ta[9]!, hf,
        Lean.mkFVar hd.fvarId])
      Lean.Elab.Tactic.replaceMainGoal [he.mvarId!, hg.mvarId!, hf.mvarId!]
  ·
    rfl
  ·
    run_tac
      let goal ← Lean.Elab.Tactic.getMainGoal
      goal.withContext do
        let target := (← Lean.instantiateMVars (← goal.getType)).consumeMData
        let a := target.getAppArgs
        unless target.getAppFn.isConstOf ``HEq && a.size == 4 do
          throwError "Expected normed-group HEq"
        let mut lhs := a[1]!.consumeMData
        let mut rhs := a[3]!.consumeMData
        -- Unfold only a direct group alias, never a space or operator norm.
        for name in #[``weakHeaderSelfDualGroup, ``weakHeaderH1DualZeroGroup, ``weakHeaderDualZeroH1ZeroGroup] do
          if lhs.getAppFn.isConstOf name then
            let ci ← Lean.getConstInfo name
            let some body := ci.value? | throwError "Simple group body unavailable"
            lhs := body.consumeMData
          if rhs.getAppFn.isConstOf name then
            let ci ← Lean.getConstInfo name
            let some body := ci.value? | throwError "Simple group body unavailable"
            rhs := body.consumeMData
        let la := lhs.getAppArgs
        let ra := rhs.getAppArgs
        unless lhs.getAppFn.isConstOf ``ContinuousLinearMap.toNormedAddCommGroup &&
            rhs.getAppFn.isConstOf ``ContinuousLinearMap.toNormedAddCommGroup &&
            la.size == 12 && ra.size == 12 do
          throwError "Expected exact twelve-argument normed CLM constructors"
        for n in (#[0,1,6,7,10] : Array Nat) do
          unless la[n]! == ra[n]! do
            throwError "Fixed scalar constructor data changed at {n}"
        let eE ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkEq la[2]! ra[2]!)
        let eF ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkEq la[3]! ra[3]!)
        let hgE ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkHEq la[4]! ra[4]!)
        let hgF ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkHEq la[5]! ra[5]!)
        let hsE ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkHEq la[8]! ra[8]!)
        let hsF ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkHEq la[9]! ra[9]!)
        let ci ← Lean.getConstInfo ``clm_normedAddCommGroup_constructor_heq
        let c := Lean.mkConst ``clm_normedAddCommGroup_constructor_heq
          (ci.levelParams.map (fun _ => Lean.Level.zero))
        goal.assign (Lean.mkAppN c #[la[0]!, la[1]!, la[2]!, ra[2]!, la[3]!, ra[3]!,
          la[6]!, la[7]!, la[4]!, ra[4]!, la[5]!, ra[5]!,
          la[8]!, ra[8]!, la[9]!, ra[9]!, la[10]!, la[11]!, ra[11]!,
          eE, eF, hgE, hgF, hsE, hsF])
        Lean.Elab.Tactic.replaceMainGoal
          [eE.mvarId!, eF.mvarId!, hgE.mvarId!, hgF.mvarId!, hsE.mvarId!, hsF.mvarId!]
    ·
      rfl
    ·
      rfl
    ·
      rfl
    ·
      rfl
    ·
      rfl
    ·
      rfl
  ·
    rfl


attribute [local irreducible] functionalInverse nativeZeroFunctionalInverse
  nativeCoefficientWeakFunctionalInverse nativeWeakHalfLift
  referenceTwoAngleWeakEnergyFamily referenceTwoAngleWeakDirichletEnergyFamily

private def nativeTwoAngleWeakHalfAffineLiftFact :=
  contDiffAt_nativeParameterWeakHalfAffineLiftFormula
    (P := ℝ × (ℝ × (ℝ × (R3 × ℝ))))

private lemma contDiffAt_real_carrier_transport
    {P E F : Type} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (g : NormedAddCommGroup E) (h : NormedAddCommGroup F)
    (s : @NormedSpace ℝ E _ g.toSeminormedAddCommGroup)
    (t : @NormedSpace ℝ F _ h.toSeminormedAddCommGroup)
    (e : E = F) (hg : HEq g h) (f : P → E) (k : P → F)
    (hf : HEq f k) (x y : P) (hxy : x = y)
    (hc : letI := g; letI := s; ContDiffAt ℝ ∞ f x) :
    letI := h; letI := t; ContDiffAt ℝ ∞ k y := by
  subst F
  have hgh : g = h := eq_of_heq hg
  cases hgh
  letI := g
  cases real_normedSpace_eq s t
  have hfk : f = k := eq_of_heq hf
  cases hfk
  cases hxy
  exact hc


private def referenceTwoAngleNativeWeakHalfInputAProof
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner) (i j k l : Fin 3)
    (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) := by
  let A := referenceTwoAngleWeakDirichletEnergyFamily
    g L y0 Φ B ε C ρ H a w hData hcalc i j k l
  let RR := referenceTwoAngleWeakEnergyFamily
    g L y0 Φ B ε C ρ H a w hData hcalc i j k l
  have hc := contDiff_referenceTwoAngleWeakDirichletEnergyFamily_nativeCanonical
    g L y0 Φ B ε C ρ H a w hData hcalc i j k l
  have hAt := hc.contDiffAt (x := t)
  have hFact := nativeTwoAngleWeakHalfAffineLiftFact
  run_tac
    let goal ← Lean.Elab.Tactic.getMainGoal
    goal.withContext do
      let ctx ← Lean.getLCtx
      let mut args : Array Lean.Expr := #[]
      for n in #[`A,`RR,`hF,`t] do
        let some ld := ctx.findFromUserName? n | throwError "Missing formula argument {n}"
        args := args.push (Lean.mkFVar ld.fvarId)
      let some fd := ctx.findFromUserName? `hFact | throwError "Missing fact"
      let mut fact := Lean.mkAppN (Lean.mkFVar fd.fvarId) args
      pure ()
      let fty ← Lean.Meta.whnf (← Lean.Meta.inferType fact)
      unless fty.isForall do throwError "Expected exact input binder"
      unless ← Lean.Meta.isDefEq (← goal.getType) fty.bindingDomain! do
        throwError "Exact input type inference failed"
      let some hd := ctx.findFromUserName? `hAt | throwError "Source continuity missing"
      let result := Lean.mkFVar hd.fvarId
      let source := (← Lean.instantiateMVars (← Lean.Meta.inferType result)).consumeMData
      let target := (← Lean.instantiateMVars (← goal.getType)).consumeMData
      let sa := source.getAppArgs
      let ta := target.getAppArgs
      unless source.getAppFn.isConstOf ``ContDiffAt &&
          target.getAppFn.isConstOf ``ContDiffAt && sa.size == 11 && ta.size == 11 do
        throwError "Expected exact ContDiffAt applications"
      let he ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkEq sa[5]! ta[5]!)
      let hg ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkHEq sa[6]! ta[6]!)
      let hf ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkHEq sa[9]! ta[9]!)
      let hp ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkEq sa[10]! ta[10]!)
      let ci ← Lean.getConstInfo ``contDiffAt_real_carrier_transport
      let c := Lean.mkConst ``contDiffAt_real_carrier_transport
        (ci.levelParams.map (fun _ => Lean.Level.zero))
      goal.assign (Lean.mkAppN c #[ta[2]!, sa[5]!, ta[5]!, ta[3]!, ta[4]!,
        sa[6]!, ta[6]!, sa[7]!, ta[7]!, he, hg, sa[9]!, ta[9]!, hf,
        sa[10]!, ta[10]!, hp, result])
      Lean.Elab.Tactic.replaceMainGoal
        [he.mvarId!, hg.mvarId!, hf.mvarId!, hp.mvarId!]
  ·
    rfl
  ·
    run_tac
      let goal ← Lean.Elab.Tactic.getMainGoal
      goal.withContext do
        let target := (← Lean.instantiateMVars (← goal.getType)).consumeMData
        let a := target.getAppArgs
        unless target.getAppFn.isConstOf ``HEq && a.size == 4 do
          throwError "Expected normed-group HEq"
        let mut lhs := a[1]!.consumeMData
        let mut rhs := a[3]!.consumeMData
        -- Unfold only a direct group alias, never a space or operator norm.
        for name in #[``weakHeaderSelfDualGroup, ``weakHeaderH1DualZeroGroup, ``weakHeaderDualZeroH1ZeroGroup] do
          if lhs.getAppFn.isConstOf name then
            let ci ← Lean.getConstInfo name
            let some body := ci.value? | throwError "Simple group body unavailable"
            lhs := body.consumeMData
          if rhs.getAppFn.isConstOf name then
            let ci ← Lean.getConstInfo name
            let some body := ci.value? | throwError "Simple group body unavailable"
            rhs := body.consumeMData
        let la := lhs.getAppArgs
        let ra := rhs.getAppArgs
        unless lhs.getAppFn.isConstOf ``ContinuousLinearMap.toNormedAddCommGroup &&
            rhs.getAppFn.isConstOf ``ContinuousLinearMap.toNormedAddCommGroup &&
            la.size == 12 && ra.size == 12 do
          throwError "Expected exact twelve-argument normed CLM constructors"
        for n in (#[0,1,6,7,10] : Array Nat) do
          unless la[n]! == ra[n]! do
            throwError "Fixed scalar constructor data changed at {n}"
        let eE ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkEq la[2]! ra[2]!)
        let eF ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkEq la[3]! ra[3]!)
        let hgE ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkHEq la[4]! ra[4]!)
        let hgF ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkHEq la[5]! ra[5]!)
        let hsE ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkHEq la[8]! ra[8]!)
        let hsF ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkHEq la[9]! ra[9]!)
        let ci ← Lean.getConstInfo ``clm_normedAddCommGroup_constructor_heq
        let c := Lean.mkConst ``clm_normedAddCommGroup_constructor_heq
          (ci.levelParams.map (fun _ => Lean.Level.zero))
        goal.assign (Lean.mkAppN c #[la[0]!, la[1]!, la[2]!, ra[2]!, la[3]!, ra[3]!,
          la[6]!, la[7]!, la[4]!, ra[4]!, la[5]!, ra[5]!,
          la[8]!, ra[8]!, la[9]!, ra[9]!, la[10]!, la[11]!, ra[11]!,
          eE, eF, hgE, hgF, hsE, hsF])
        Lean.Elab.Tactic.replaceMainGoal
          [eE.mvarId!, eF.mvarId!, hgE.mvarId!, hgF.mvarId!, hsE.mvarId!, hsF.mvarId!]
    ·
      rfl
    ·
      rfl
    ·
      rfl
    ·
      rfl
    ·
      rfl
    ·
      rfl
  ·
    rfl
  ·
    rfl

private def referenceTwoAngleNativeWeakHalfInputRProof
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner) (i j k l : Fin 3)
    (t : ℝ × (ℝ × (ℝ × (R3 × ℝ)))) := by
  let A := referenceTwoAngleWeakDirichletEnergyFamily
    g L y0 Φ B ε C ρ H a w hData hcalc i j k l
  let RR := referenceTwoAngleWeakEnergyFamily
    g L y0 Φ B ε C ρ H a w hData hcalc i j k l
  have hc := contDiff_referenceTwoAngleWeakEnergyFamily_nativeCanonical
    g L y0 Φ B ε C ρ H a w hData hcalc i j k l
  have hAt := hc.contDiffAt (x := t)
  have hFact := nativeTwoAngleWeakHalfAffineLiftFact
  run_tac
    let goal ← Lean.Elab.Tactic.getMainGoal
    goal.withContext do
      let ctx ← Lean.getLCtx
      let mut args : Array Lean.Expr := #[]
      for n in #[`A,`RR,`hF,`t] do
        let some ld := ctx.findFromUserName? n | throwError "Missing formula argument {n}"
        args := args.push (Lean.mkFVar ld.fvarId)
      let some fd := ctx.findFromUserName? `hFact | throwError "Missing fact"
      let mut fact := Lean.mkAppN (Lean.mkFVar fd.fvarId) args
      let first ← Lean.Meta.whnf (← Lean.Meta.inferType fact)
      unless first.isForall do throwError "Expected first input binder"
      let ha ← Lean.Meta.mkFreshExprMVar first.bindingDomain!
      fact := Lean.mkApp fact ha
      let fty ← Lean.Meta.whnf (← Lean.Meta.inferType fact)
      unless fty.isForall do throwError "Expected exact input binder"
      unless ← Lean.Meta.isDefEq (← goal.getType) fty.bindingDomain! do
        throwError "Exact input type inference failed"
      let some hd := ctx.findFromUserName? `hAt | throwError "Source continuity missing"
      let result := Lean.mkFVar hd.fvarId
      let source := (← Lean.instantiateMVars (← Lean.Meta.inferType result)).consumeMData
      let target := (← Lean.instantiateMVars (← goal.getType)).consumeMData
      let sa := source.getAppArgs
      let ta := target.getAppArgs
      unless source.getAppFn.isConstOf ``ContDiffAt &&
          target.getAppFn.isConstOf ``ContDiffAt && sa.size == 11 && ta.size == 11 do
        throwError "Expected exact ContDiffAt applications"
      let he ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkEq sa[5]! ta[5]!)
      let hg ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkHEq sa[6]! ta[6]!)
      let hf ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkHEq sa[9]! ta[9]!)
      let hp ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkEq sa[10]! ta[10]!)
      let ci ← Lean.getConstInfo ``contDiffAt_real_carrier_transport
      let c := Lean.mkConst ``contDiffAt_real_carrier_transport
        (ci.levelParams.map (fun _ => Lean.Level.zero))
      goal.assign (Lean.mkAppN c #[ta[2]!, sa[5]!, ta[5]!, ta[3]!, ta[4]!,
        sa[6]!, ta[6]!, sa[7]!, ta[7]!, he, hg, sa[9]!, ta[9]!, hf,
        sa[10]!, ta[10]!, hp, result])
      Lean.Elab.Tactic.replaceMainGoal
        [he.mvarId!, hg.mvarId!, hf.mvarId!, hp.mvarId!]
  ·
    rfl
  ·
    run_tac
      let goal ← Lean.Elab.Tactic.getMainGoal
      goal.withContext do
        let target := (← Lean.instantiateMVars (← goal.getType)).consumeMData
        let a := target.getAppArgs
        unless target.getAppFn.isConstOf ``HEq && a.size == 4 do
          throwError "Expected normed-group HEq"
        let mut lhs := a[1]!.consumeMData
        let mut rhs := a[3]!.consumeMData
        -- Unfold only a direct group alias, never a space or operator norm.
        for name in #[``weakHeaderSelfDualGroup, ``weakHeaderH1DualZeroGroup, ``weakHeaderDualZeroH1ZeroGroup] do
          if lhs.getAppFn.isConstOf name then
            let ci ← Lean.getConstInfo name
            let some body := ci.value? | throwError "Simple group body unavailable"
            lhs := body.consumeMData
          if rhs.getAppFn.isConstOf name then
            let ci ← Lean.getConstInfo name
            let some body := ci.value? | throwError "Simple group body unavailable"
            rhs := body.consumeMData
        let la := lhs.getAppArgs
        let ra := rhs.getAppArgs
        unless lhs.getAppFn.isConstOf ``ContinuousLinearMap.toNormedAddCommGroup &&
            rhs.getAppFn.isConstOf ``ContinuousLinearMap.toNormedAddCommGroup &&
            la.size == 12 && ra.size == 12 do
          throwError "Expected exact twelve-argument normed CLM constructors"
        for n in (#[0,1,6,7,10] : Array Nat) do
          unless la[n]! == ra[n]! do
            throwError "Fixed scalar constructor data changed at {n}"
        let eE ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkEq la[2]! ra[2]!)
        let eF ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkEq la[3]! ra[3]!)
        let hgE ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkHEq la[4]! ra[4]!)
        let hgF ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkHEq la[5]! ra[5]!)
        let hsE ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkHEq la[8]! ra[8]!)
        let hsF ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkHEq la[9]! ra[9]!)
        let ci ← Lean.getConstInfo ``clm_normedAddCommGroup_constructor_heq
        let c := Lean.mkConst ``clm_normedAddCommGroup_constructor_heq
          (ci.levelParams.map (fun _ => Lean.Level.zero))
        goal.assign (Lean.mkAppN c #[la[0]!, la[1]!, la[2]!, ra[2]!, la[3]!, ra[3]!,
          la[6]!, la[7]!, la[4]!, ra[4]!, la[5]!, ra[5]!,
          la[8]!, ra[8]!, la[9]!, ra[9]!, la[10]!, la[11]!, ra[11]!,
          eE, eF, hgE, hgF, hsE, hsF])
        Lean.Elab.Tactic.replaceMainGoal
          [eE.mvarId!, eF.mvarId!, hgE.mvarId!, hgF.mvarId!, hsE.mvarId!, hsF.mvarId!]
    ·
      rfl
    ·
      rfl
    ·
      rfl
    ·
      rfl
    ·
      rfl
    ·
      rfl
  ·
    rfl
  ·
    rfl

private def referenceTwoAngleWeakHalfAffineCanonicalProof
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner) (i j k l : Fin 3)
    (t : ℝ × (ℝ × (ℝ × (R3 × ℝ))))
    (hOriginal : (referenceWeakDirichletEnergyFamily
      g L y0 Φ B ε C ρ H a w hData hcalc t.2.2).IsInvertible) := by
  let A := referenceTwoAngleWeakDirichletEnergyFamily
    g L y0 Φ B ε C ρ H a w hData hcalc i j k l
  let RR := referenceTwoAngleWeakEnergyFamily
    g L y0 Φ B ε C ρ H a w hData hcalc i j k l
  have hAc := contDiff_referenceTwoAngleWeakDirichletEnergyFamily_nativeCanonical
    g L y0 Φ B ε C ρ H a w hData hcalc i j k l
  have hRc := contDiff_referenceTwoAngleWeakEnergyFamily_nativeCanonical
    g L y0 Φ B ε C ρ H a w hData hcalc i j k l
  have hFact := nativeTwoAngleWeakHalfAffineLiftFact
  run_tac
    let goal ← Lean.Elab.Tactic.getMainGoal
    goal.withContext do
      let ctx ← Lean.getLCtx
      let mut args : Array Lean.Expr := #[]
      for n in #[`A,`RR,`hF,`t] do
        let some ld := ctx.findFromUserName? n | throwError "Missing formula argument {n}"
        args := args.push (Lean.mkFVar ld.fvarId)
      let some ld := ctx.findFromUserName? `hFact | throwError "Missing generic fact"
      let mut result := Lean.mkAppN (Lean.mkFVar ld.fvarId) args
      let mut goals : List Lean.MVarId := []
      for _ in [:3] do
        let ty ← Lean.Meta.whnf (← Lean.Meta.inferType result)
        unless ty.isForall do throwError "Expected exact A/R/invertibility binder"
        let h ← Lean.Meta.mkFreshExprMVar ty.bindingDomain!
        result := Lean.mkApp result h
        goals := goals ++ [h.mvarId!]
      unless ← Lean.Meta.isDefEq (← goal.getType) (← Lean.Meta.inferType result) do
        throwError "Canonical formula result type mismatch"
      goal.assign result
      Lean.Elab.Tactic.replaceMainGoal goals
  ·
    exact referenceTwoAngleNativeWeakHalfInputAProof
      g L y0 Φ B ε C ρ H a w hData hcalc hF i j k l t
  ·
    exact referenceTwoAngleNativeWeakHalfInputRProof
      g L y0 Φ B ε C ρ H a w hData hcalc hF i j k l t
  ·
    exact referenceTwoAngleWeakDirichletEnergyFamily_isInvertible_of_original
      g L y0 Φ B ε C ρ H a w hData hcalc i j k l t.1 t.2.1 t.2.2 hOriginal

end NativeWeakHalfCanonicalInputs

attribute [local irreducible] functionalInverse nativeZeroFunctionalInverse
  nativeCoefficientWeakFunctionalInverse nativeWeakHalfLift
  referenceTwoAngleWeakEnergyFamily referenceTwoAngleWeakDirichletEnergyFamily

lemma contDiffAt_referenceTwoAngleNativeWeakHalfLiftFamily_of_original
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner) (i j k l : Fin 3)
    (t : ℝ × (ℝ × (ℝ × (R3 × ℝ))))
    (hOriginal : (referenceWeakDirichletEnergyFamily
      g L y0 Φ B ε C ρ H a w hData hcalc t.2.2).IsInvertible) :
    ContDiffAt ℝ ∞ (referenceTwoAngleNativeWeakHalfLiftFamily
      g L y0 Φ B ε C ρ H a w hData hF i j k l) t := by
  have hFormula := referenceTwoAngleWeakHalfAffineCanonicalProof
    g L y0 Φ B ε C ρ H a w hData hcalc hF i j k l t hOriginal
  exact contDiffAt_nativeParameterHalfLiftFamily_congr _ _ t hFormula
    (fun z => referenceTwoAngleNativeWeakHalfLiftFamily_eq_affineFormula
      g L y0 Φ B ε C ρ H a w hData hcalc hF i j k l z)

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceTwoAngleNativeWeakHalfLiftFamily_of_original
