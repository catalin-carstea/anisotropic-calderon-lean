import Calderon.NativeWeakOperatorNormedStructures
import Calderon.ActualReferenceRotationWeakEnergy
import Calderon.InheritedNormedStructureData
import Calderon.ClmInheritedStructureData
import Calderon.LpInheritedStructureData

set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ContDiff ENNReal Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError

-- Type 0 is intentional: these are the actual concrete carriers in this focus.
private lemma continuous_topology_carrier_transport
    {P Q E F : Type}
    (p : TopologicalSpace P) (q : TopologicalSpace Q)
    (s : TopologicalSpace E) (t : TopologicalSpace F)
    (ep : P = Q) (ee : E = F) (hp : HEq p q) (hs : HEq s t)
    (f : P → E) (k : Q → F) (hf : HEq f k)
    (hc : @Continuous P E p s f) : @Continuous Q F q t k := by
  subst Q
  subst F
  cases eq_of_heq hp
  cases eq_of_heq hs
  cases eq_of_heq hf
  exact hc

private lemma continuous_of_real_contDiff_carrier
    {E F : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (hf : ContDiff ℝ ∞ f) : Continuous f := hf.continuous

-- Congruence only for the dictionaries actually differing in v033.
-- No norm or space is identified by fiat: all six equalities are obligations.
private lemma real_clm_carrier_eq
    {E F : Type}
    (tE tE' : TopologicalSpace E) (aE aE' : AddCommMonoid E)
    (tF tF' : TopologicalSpace F) (aF aF' : AddCommMonoid F)
    (mE : @Module ℝ E Real.semiring aE)
    (mE' : @Module ℝ E Real.semiring aE')
    (mF : @Module ℝ F Real.semiring aF)
    (mF' : @Module ℝ F Real.semiring aF')
    (htE : tE = tE') (haE : aE = aE')
    (htF : tF = tF') (haF : aF = aF')
    (hmE : HEq mE mE') (hmF : HEq mF mF') :
    @ContinuousLinearMap ℝ ℝ Real.semiring Real.semiring (RingHom.id ℝ)
      E tE aE F tF aF mE mF =
    @ContinuousLinearMap ℝ ℝ Real.semiring Real.semiring (RingHom.id ℝ)
      E tE' aE' F tF' aF' mE' mF' := by
  cases htE
  cases haE
  cases htF
  cases haF
  have he : mE = mE' := eq_of_heq hmE
  cases he
  have hf : mF = mF' := eq_of_heq hmF
  cases hf
  rfl

private lemma real_clm_normedAddCommGroup_addCommMonoid_eq_natural
    (U K : Type) [NormedAddCommGroup U] [NormedAddCommGroup K]
    [NormedSpace ℝ U] [NormedSpace ℝ K] :
    (ContinuousLinearMap.toNormedAddCommGroup
      (E := U) (F := K) (σ₁₂ := RingHom.id ℝ)).toAddCommGroup.toAddCommMonoid =
    ContinuousLinearMap.addCommMonoid
      (M₁ := U) (M₂ := K) (σ₁₂ := RingHom.id ℝ) := by
  have hSemi := clm_normedAddCommGroup_seminormedAddCommGroup_eq U K
  have hAdd := congrArg
    (fun n : SeminormedAddCommGroup (U →L[ℝ] K) =>
      n.toAddCommGroup.toAddCommMonoid) hSemi
  exact hAdd.trans (clm_seminormedAddCommGroup_addCommMonoid_eq_natural U K)

private lemma real_clm_normedSpace_module_heq_natural
    (U K : Type) [SeminormedAddCommGroup U] [SeminormedAddCommGroup K]
    [NormedSpace ℝ U] [NormedSpace ℝ K] :
    HEq (ContinuousLinearMap.module (S₃ := ℝ) (M := U) (M₃ := K) (σ₁₃ := RingHom.id ℝ))
      (ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
        (E := U) (F := K) (σ₁₂ := RingHom.id ℝ)).toModule := by
  exact heq_of_eq (clm_normedSpace_module_eq_natural U K).symm

private lemma real_clm_normedAddCommGroup_topology_eq_natural
    (U K : Type) [NormedAddCommGroup U] [NormedAddCommGroup K]
    [NormedSpace ℝ U] [NormedSpace ℝ K] :
    (ContinuousLinearMap.toNormedAddCommGroup
      (E := U) (F := K) (σ₁₂ := RingHom.id ℝ)).toSeminormedAddCommGroup.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace =
    ContinuousLinearMap.topologicalSpace
      (E := U) (F := K) (σ := RingHom.id ℝ) := by
  have hSemi := clm_normedAddCommGroup_seminormedAddCommGroup_eq U K
  have hTop := congrArg
    (fun n : SeminormedAddCommGroup (U →L[ℝ] K) =>
      n.toPseudoMetricSpace.toUniformSpace.toTopologicalSpace) hSemi
  exact hTop.trans (clm_seminormedAddCommGroup_topologicalSpace_eq_natural U K)

private lemma real_clm_isInvertible_eq
    {E F : Type}
    (tE tE' : TopologicalSpace E) (aE aE' : AddCommMonoid E)
    (tF tF' : TopologicalSpace F) (aF aF' : AddCommMonoid F)
    (mE : @Module ℝ E Real.semiring aE)
    (mE' : @Module ℝ E Real.semiring aE')
    (mF : @Module ℝ F Real.semiring aF)
    (mF' : @Module ℝ F Real.semiring aF')
    (htE : tE = tE') (haE : aE = aE')
    (htF : tF = tF') (haF : aF = aF')
    (hmE : HEq mE mE') (hmF : HEq mF mF')
    (f : @ContinuousLinearMap ℝ ℝ Real.semiring Real.semiring (RingHom.id ℝ)
      E tE aE F tF aF mE mF)
    (g : @ContinuousLinearMap ℝ ℝ Real.semiring Real.semiring (RingHom.id ℝ)
      E tE' aE' F tF' aF' mE' mF') (hf : HEq f g) :
    @ContinuousLinearMap.IsInvertible ℝ E F tE tF Real.semiring aE mE aF mF f =
    @ContinuousLinearMap.IsInvertible ℝ E F tE' tF' Real.semiring aE' mE' aF' mF' g := by
  cases htE
  cases haE
  cases htF
  cases haF
  cases eq_of_heq hmE
  cases eq_of_heq hmF
  cases eq_of_heq hf
  rfl

attribute [local instance] TauCeti.W1p0.instNormedAddCommGroup TauCeti.W1p0.instInnerProductSpace
attribute [local instance] weakHeaderDualZeroGroup weakHeaderDualZeroSpace
attribute [local instance] weakHeaderSelfDualGroup weakHeaderSelfDualSpace

-- Same existing proof specialization, isolated to give each declaration the unchanged budget.
private def nativeTwoAngleInverseOpenFact :=
  isOpen_clm_inverse_preimage
    (P := (ℝ × (ℝ × (ℝ × (R3 × ℝ))))) (U := BallH1Zero) (V := StrongDual ℝ BallH1Zero)

lemma isOpen_nativeTwoAngle_inverse_preimage_canonical
    (A : (ℝ × (ℝ × (ℝ × (R3 × ℝ)))) → BallH1Zero →L[ℝ] StrongDual ℝ BallH1Zero)
    (hA : ContDiff ℝ ∞ A) : IsOpen {t | (A t).IsInvertible} := by
  have hOpen := nativeTwoAngleInverseOpenFact
  run_tac
    let goal ← Lean.Elab.Tactic.getMainGoal
    goal.withContext do
      let ctx ← Lean.getLCtx
      let some hd := ctx.findFromUserName? `hA | throwError "hA missing"
      let source := (← Lean.instantiateMVars hd.type).consumeMData
      let sa := source.getAppArgs
      unless sa.size == 10 do throwError "Expected ten ContDiff arguments"
      let ci ← Lean.getConstInfo ``continuous_of_real_contDiff_carrier
      let c := Lean.mkConst ``continuous_of_real_contDiff_carrier
        (ci.levelParams.map (fun _ => Lean.Level.zero))
      let hc := Lean.mkAppN c #[sa[2]!, sa[5]!, sa[3]!, sa[4]!,
        sa[6]!, sa[7]!, sa[9]!, Lean.mkFVar hd.fvarId]
      let ht ← Lean.Meta.inferType hc
      let next ← goal.assert `hC ht hc
      let (_, next) ← next.intro1P
      Lean.Elab.Tactic.replaceMainGoal [next]
  -- Do not elaborate hOpen A hC against an expected type. Build its raw
  -- application, expose the exact Continuous argument as a separate goal,
  -- and expose any final IsOpen proposition conversion as an equality.
  run_tac
    let goal ← Lean.Elab.Tactic.getMainGoal
    goal.withContext do
      let ctx ← Lean.getLCtx
      let some ho := ctx.findFromUserName? `hOpen | throwError "hOpen missing"
      let some ad := ctx.findFromUserName? `A | throwError "A missing"
      let openApplication := Lean.mkApp (Lean.mkFVar ho.fvarId) (Lean.mkFVar ad.fvarId)
      Lean.logInfo "RAW_OPEN_APPLICATION"
      let partialType ← Lean.Meta.whnf (← Lean.Meta.inferType openApplication)
      unless partialType.isForall do throwError "hOpen A is not a binder"
      Lean.logInfo "RAW_OPEN_EXPECTED_CONTINUITY"
      let hc ← Lean.Meta.mkFreshExprMVar partialType.bindingDomain!
      let result := Lean.mkApp openApplication hc
      let resultType ← Lean.Meta.inferType result
      let target ← goal.getType
      let he ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkEq resultType target)
      let ci ← Lean.getConstInfo ``Eq.mp
      let mp := Lean.mkConst ``Eq.mp (ci.levelParams.map (fun _ => Lean.Level.zero))
      goal.assign (Lean.mkAppN mp #[resultType, target, he, result])
      Lean.Elab.Tactic.replaceMainGoal [hc.mvarId!, he.mvarId!]
  ·
    run_tac
      let goal ← Lean.Elab.Tactic.getMainGoal
      goal.withContext do
        let target := (← Lean.instantiateMVars (← goal.getType)).consumeMData
        let ctx ← Lean.getLCtx
        let some hd := ctx.findFromUserName? `hC | throwError "hC missing"
        let source := (← Lean.instantiateMVars hd.type).consumeMData
        let sa := source.getAppArgs
        let ta := target.getAppArgs
        unless source.getAppFn.isConstOf ``Continuous &&
            target.getAppFn.isConstOf ``Continuous && sa.size == 5 && ta.size == 5 do
          throwError "Expected exact five-argument Continuous applications"
        let ep ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkEq sa[0]! ta[0]!)
        let ee ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkEq sa[1]! ta[1]!)
        let hp ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkHEq sa[2]! ta[2]!)
        let hs ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkHEq sa[3]! ta[3]!)
        let hf ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkHEq sa[4]! ta[4]!)
        let ci ← Lean.getConstInfo ``continuous_topology_carrier_transport
        let c := Lean.mkConst ``continuous_topology_carrier_transport
          (ci.levelParams.map (fun _ => Lean.Level.zero))
        goal.assign (Lean.mkAppN c #[sa[0]!, ta[0]!, sa[1]!, ta[1]!,
          sa[2]!, ta[2]!, sa[3]!, ta[3]!, ep, ee, hp, hs,
          sa[4]!, ta[4]!, hf, Lean.mkFVar hd.fvarId])
        Lean.Elab.Tactic.replaceMainGoal
          [ep.mvarId!, ee.mvarId!, hp.mvarId!, hs.mvarId!, hf.mvarId!]
    ·
      rfl
    ·
      run_tac
        let goal ← Lean.Elab.Tactic.getMainGoal
        goal.withContext do
          let target := (← Lean.instantiateMVars (← goal.getType)).consumeMData
          let ea := target.getAppArgs
          unless target.getAppFn.isConstOf ``Eq && ea.size == 3 do
            throwError "Expected carrier equality"
          let sourceCarrier := ea[1]!.consumeMData
          let targetCarrier := ea[2]!.consumeMData
          let sa := sourceCarrier.getAppArgs
          let ta := targetCarrier.getAppArgs
          unless sourceCarrier.getAppFn.isConstOf ``ContinuousLinearMap &&
              targetCarrier.getAppFn.isConstOf ``ContinuousLinearMap &&
              sa.size == 13 && ta.size == 13 do
            throwError "Expected exact 13-argument CLM carriers"
          for i in (#[0, 1, 2, 3, 4, 5, 8] : Array Nat) do
            unless sa[i]! == ta[i]! do
              throwError "Previously identical CLM carrier argument changed: {i}"
          let h6 ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkEq sa[6]! ta[6]!)
          let h7 ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkEq sa[7]! ta[7]!)
          let h9 ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkEq sa[9]! ta[9]!)
          let h10 ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkEq sa[10]! ta[10]!)
          let h11 ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkHEq sa[11]! ta[11]!)
          let h12 ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkHEq sa[12]! ta[12]!)
          let ci ← Lean.getConstInfo ``real_clm_carrier_eq
          let c := Lean.mkConst ``real_clm_carrier_eq
            (ci.levelParams.map (fun _ => Lean.Level.zero))
          goal.assign (Lean.mkAppN c #[sa[5]!, sa[8]!,
            sa[6]!, ta[6]!, sa[7]!, ta[7]!, sa[9]!, ta[9]!,
            sa[10]!, ta[10]!, sa[11]!, ta[11]!, sa[12]!, ta[12]!,
            h6, h7, h9, h10, h11, h12])
          Lean.Elab.Tactic.replaceMainGoal
            [h6.mvarId!, h7.mvarId!, h9.mvarId!, h10.mvarId!, h11.mvarId!, h12.mvarId!]
      ·
        rfl
      ·
        rfl
      ·
        rfl
      ·
        run_tac
          let goal ← Lean.Elab.Tactic.getMainGoal
          goal.withContext do
            -- This definition is a direct library instance application. Inspect
            -- its arguments, not its normed-group proof or the SelfDualSpace.
            let di ← Lean.getConstInfo ``weakHeaderDualZeroGroup
            let some body := di.value? | throwError "DualZero group body unavailable"
            let body := body.consumeMData
            unless body.getAppFn.isConstOf ``ContinuousLinearMap.toNormedAddCommGroup do
              throwError "DualZero group is not the expected direct CLM instance"
            let mut groups : Array (Lean.Expr × Lean.Expr) := #[]
            let mut spaces : Array (Lean.Expr × Lean.Expr) := #[]
            for a in body.getAppArgs do
              let ty := (← Lean.Meta.inferType a).consumeMData
              let aa := ty.getAppArgs
              if ty.getAppFn.isConstOf ``NormedAddCommGroup && aa.size == 1 then
                groups := groups.push (aa[0]!, a)
              if ty.getAppFn.isConstOf ``NormedSpace && aa.size == 4 then
                spaces := spaces.push (aa[1]!, a)
            unless groups.size == 2 do
              throwError "Expected exact source/codomain normed groups in DualZero body"
            let u := groups[0]!.1
            let k := groups[1]!.1
            let mut su? : Option Lean.Expr := none
            let mut sk? : Option Lean.Expr := none
            for entry in spaces do
              if entry.1 == u then su? := some entry.2
              if entry.1 == k then sk? := some entry.2
            let some su := su? | throwError "Source normed space missing"
            let some sk := sk? | throwError "Codomain normed space missing"
            let ci ← Lean.getConstInfo ``real_clm_normedAddCommGroup_addCommMonoid_eq_natural
            let c := Lean.mkConst ``real_clm_normedAddCommGroup_addCommMonoid_eq_natural
              (ci.levelParams.map (fun _ => Lean.Level.zero))
            let proof := Lean.mkAppN c #[u, k, groups[0]!.2, groups[1]!.2, su, sk]
            let proofType := (← Lean.Meta.inferType proof).consumeMData
            let ea := proofType.getAppArgs
            unless proofType.getAppFn.isConstOf ``Eq && ea.size == 3 do
              throwError "Expected exact additive projection certificate"
            let si ← Lean.getConstInfo ``Eq.symm
            let symm := Lean.mkConst ``Eq.symm
              (si.levelParams.map (fun _ => Lean.Level.succ Lean.Level.zero))
            goal.assign (Lean.mkAppN symm #[ea[0]!, ea[1]!, ea[2]!, proof])
      ·
        rfl
      ·
        run_tac
          let goal ← Lean.Elab.Tactic.getMainGoal
          goal.withContext do
            let di ← Lean.getConstInfo ``weakHeaderDualZeroSpace
            let some body := di.value? | throwError "DualZero space body unavailable"
            let body := body.consumeMData
            unless body.getAppFn.isConstOf ``ContinuousLinearMap.toNormedSpace do
              throwError "DualZero space is not the expected direct CLM instance"
            let mut groups : Array (Lean.Expr × Lean.Expr) := #[]
            let mut spaces : Array (Lean.Expr × Lean.Expr) := #[]
            for a in body.getAppArgs do
              let ty := (← Lean.Meta.inferType a).consumeMData
              let aa := ty.getAppArgs
              if ty.getAppFn.isConstOf ``SeminormedAddCommGroup && aa.size == 1 then
                groups := groups.push (aa[0]!, a)
              if ty.getAppFn.isConstOf ``NormedSpace && aa.size == 4 then
                spaces := spaces.push (aa[1]!, a)
            unless groups.size == 2 do
              throwError "Expected two exact seminormed groups in DualZero space body"
            let u := groups[0]!.1
            let k := groups[1]!.1
            let mut su? : Option Lean.Expr := none
            let mut sk? : Option Lean.Expr := none
            for entry in spaces do
              if entry.1 == u then su? := some entry.2
              if entry.1 == k then sk? := some entry.2
            let some su := su? | throwError "Source normed space missing"
            let some sk := sk? | throwError "Codomain normed space missing"
            let ci ← Lean.getConstInfo ``real_clm_normedSpace_module_heq_natural
            let c := Lean.mkConst ``real_clm_normedSpace_module_heq_natural
              (ci.levelParams.map (fun _ => Lean.Level.zero))
            goal.assign (Lean.mkAppN c #[u,k,groups[0]!.2,groups[1]!.2,su,sk])
    ·
      rfl
    ·
      run_tac
        let goal ← Lean.Elab.Tactic.getMainGoal
        goal.withContext do
          -- This definition is a direct library instance application. Inspect
          -- its arguments, not its normed-group proof or the SelfDualSpace.
          let di ← Lean.getConstInfo ``weakHeaderSelfDualGroup
          let some body := di.value? | throwError "SelfDual group body unavailable"
          let body := body.consumeMData
          unless body.getAppFn.isConstOf ``ContinuousLinearMap.toNormedAddCommGroup do
            throwError "SelfDual group is not the expected direct CLM instance"
          let mut groups : Array (Lean.Expr × Lean.Expr) := #[]
          let mut spaces : Array (Lean.Expr × Lean.Expr) := #[]
          for a in body.getAppArgs do
            let ty := (← Lean.Meta.inferType a).consumeMData
            let aa := ty.getAppArgs
            if ty.getAppFn.isConstOf ``NormedAddCommGroup && aa.size == 1 then
              groups := groups.push (aa[0]!, a)
            if ty.getAppFn.isConstOf ``NormedSpace && aa.size == 4 then
              spaces := spaces.push (aa[1]!, a)
          unless groups.size == 2 do
            throwError "Expected exact source/codomain normed groups in SelfDual body"
          let u := groups[0]!.1
          let k := groups[1]!.1
          let mut su? : Option Lean.Expr := none
          let mut sk? : Option Lean.Expr := none
          for entry in spaces do
            if entry.1 == u then su? := some entry.2
            if entry.1 == k then sk? := some entry.2
          let some su := su? | throwError "Source normed space missing"
          let some sk := sk? | throwError "Codomain normed space missing"
          let ci ← Lean.getConstInfo ``real_clm_normedAddCommGroup_topology_eq_natural
          let c := Lean.mkConst ``real_clm_normedAddCommGroup_topology_eq_natural
            (ci.levelParams.map (fun _ => Lean.Level.zero))
          let proof := Lean.mkAppN c #[u, k, groups[0]!.2, groups[1]!.2, su, sk]
          let proofType := (← Lean.Meta.inferType proof).consumeMData
          let ea := proofType.getAppArgs
          unless proofType.getAppFn.isConstOf ``Eq && ea.size == 3 do
            throwError "Expected exact additive projection certificate"
          let hp ← Lean.Meta.mkAppM ``heq_of_eq #[proof]
          goal.assign hp

    ·
      rfl
  ·
    apply congrArg (fun pred : (ℝ × (ℝ × (ℝ × (R3 × ℝ)))) → Prop => IsOpen {p | pred p})
    funext p
    run_tac
      let goal ← Lean.Elab.Tactic.getMainGoal
      goal.withContext do
        let target := (← Lean.instantiateMVars (← goal.getType)).consumeMData
        let ea := target.getAppArgs
        let lhs := ea[1]!.consumeMData
        let rhs := ea[2]!.consumeMData
        let sa := lhs.getAppArgs
        let ta := rhs.getAppArgs
        unless lhs.getAppFn.isConstOf ``ContinuousLinearMap.IsInvertible &&
            rhs.getAppFn.isConstOf ``ContinuousLinearMap.IsInvertible && sa.size == 11 && ta.size == 11 do
          throwError "Expected exact11-argument inverse predicates"
        for i in (#[0,1,2,5,10] : Array Nat) do
          unless sa[i]! == ta[i]! do throwError "Identical inverse predicate argument changed: {i}"
        let h3 ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkEq sa[3]! ta[3]!)
        let h6 ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkEq sa[6]! ta[6]!)
        let h4 ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkEq sa[4]! ta[4]!)
        let h8 ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkEq sa[8]! ta[8]!)
        let h7 ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkHEq sa[7]! ta[7]!)
        let h9 ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkHEq sa[9]! ta[9]!)
        let hf ← Lean.Meta.mkFreshExprMVar (← Lean.Meta.mkHEq sa[10]! ta[10]!)
        let ci ← Lean.getConstInfo ``real_clm_isInvertible_eq
        let c := Lean.mkConst ``real_clm_isInvertible_eq
          (ci.levelParams.map (fun _ => Lean.Level.zero))
        goal.assign (Lean.mkAppN c #[sa[1]!,sa[2]!,sa[3]!,ta[3]!,sa[6]!,ta[6]!,
          sa[4]!,ta[4]!,sa[8]!,ta[8]!,sa[7]!,ta[7]!,sa[9]!,ta[9]!,
          h3,h6,h4,h8,h7,h9,sa[10]!,ta[10]!,hf])
        Lean.Elab.Tactic.replaceMainGoal
          [h3.mvarId!,h6.mvarId!,h4.mvarId!,h8.mvarId!,h7.mvarId!,h9.mvarId!,hf.mvarId!]
    ·
      symm
      rfl
    ·
      symm
      rfl
    ·
      symm
      rfl
    ·
      run_tac
        let goal ← Lean.Elab.Tactic.getMainGoal
        goal.withContext do
          -- This definition is a direct library instance application. Inspect
          -- its arguments, not its normed-group proof or the SelfDualSpace.
          let di ← Lean.getConstInfo ``weakHeaderDualZeroGroup
          let some body := di.value? | throwError "DualZero group body unavailable"
          let body := body.consumeMData
          unless body.getAppFn.isConstOf ``ContinuousLinearMap.toNormedAddCommGroup do
            throwError "DualZero group is not the expected direct CLM instance"
          let mut groups : Array (Lean.Expr × Lean.Expr) := #[]
          let mut spaces : Array (Lean.Expr × Lean.Expr) := #[]
          for a in body.getAppArgs do
            let ty := (← Lean.Meta.inferType a).consumeMData
            let aa := ty.getAppArgs
            if ty.getAppFn.isConstOf ``NormedAddCommGroup && aa.size == 1 then
              groups := groups.push (aa[0]!, a)
            if ty.getAppFn.isConstOf ``NormedSpace && aa.size == 4 then
              spaces := spaces.push (aa[1]!, a)
          unless groups.size == 2 do
            throwError "Expected exact source/codomain normed groups in DualZero body"
          let u := groups[0]!.1
          let k := groups[1]!.1
          let mut su? : Option Lean.Expr := none
          let mut sk? : Option Lean.Expr := none
          for entry in spaces do
            if entry.1 == u then su? := some entry.2
            if entry.1 == k then sk? := some entry.2
          let some su := su? | throwError "Source normed space missing"
          let some sk := sk? | throwError "Codomain normed space missing"
          let ci ← Lean.getConstInfo ``real_clm_normedAddCommGroup_addCommMonoid_eq_natural
          let c := Lean.mkConst ``real_clm_normedAddCommGroup_addCommMonoid_eq_natural
            (ci.levelParams.map (fun _ => Lean.Level.zero))
          let proof := Lean.mkAppN c #[u, k, groups[0]!.2, groups[1]!.2, su, sk]
          let proofType := (← Lean.Meta.inferType proof).consumeMData
          let ea := proofType.getAppArgs
          unless proofType.getAppFn.isConstOf ``Eq && ea.size == 3 do
            throwError "Expected exact additive projection certificate"
          goal.assign proof
    ·
      apply HEq.symm
      rfl
    ·
      run_tac
        let goal ← Lean.Elab.Tactic.getMainGoal
        goal.withContext do
          let di ← Lean.getConstInfo ``weakHeaderDualZeroSpace
          let some body := di.value? | throwError "DualZero space body unavailable"
          let body := body.consumeMData
          unless body.getAppFn.isConstOf ``ContinuousLinearMap.toNormedSpace do
            throwError "DualZero space is not the expected direct CLM instance"
          let mut groups : Array (Lean.Expr × Lean.Expr) := #[]
          let mut spaces : Array (Lean.Expr × Lean.Expr) := #[]
          for a in body.getAppArgs do
            let ty := (← Lean.Meta.inferType a).consumeMData
            let aa := ty.getAppArgs
            if ty.getAppFn.isConstOf ``SeminormedAddCommGroup && aa.size == 1 then
              groups := groups.push (aa[0]!, a)
            if ty.getAppFn.isConstOf ``NormedSpace && aa.size == 4 then
              spaces := spaces.push (aa[1]!, a)
          unless groups.size == 2 do
            throwError "Expected two exact seminormed groups in DualZero space body"
          let u := groups[0]!.1
          let k := groups[1]!.1
          let mut su? : Option Lean.Expr := none
          let mut sk? : Option Lean.Expr := none
          for entry in spaces do
            if entry.1 == u then su? := some entry.2
            if entry.1 == k then sk? := some entry.2
          let some su := su? | throwError "Source normed space missing"
          let some sk := sk? | throwError "Codomain normed space missing"
          let ci ← Lean.getConstInfo ``real_clm_normedSpace_module_heq_natural
          let c := Lean.mkConst ``real_clm_normedSpace_module_heq_natural
            (ci.levelParams.map (fun _ => Lean.Level.zero))
          let proof := Lean.mkAppN c #[u,k,groups[0]!.2,groups[1]!.2,su,sk]
          let rev ← Lean.Meta.mkAppM ``HEq.symm #[proof]
          goal.assign rev
    ·
      rfl

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.isOpen_nativeTwoAngle_inverse_preimage_canonical
