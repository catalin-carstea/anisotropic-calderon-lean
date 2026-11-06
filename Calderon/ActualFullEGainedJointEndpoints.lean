import Calderon.FullEUniformWithinJetCaps
import Calderon.ActualFullEGainedPairedCore
import Calderon.ActualFullEComplementarySmooth
import Calderon.ActualFullEOrdinarySmoothSelection
import Calderon.ActualFullEGainedHighBandRooms

/-! Exact actual full E/E joint endpoints. Root-authored representation boundary;
all actual RR/RH/HR/HH and zero rows, both low inclusion graphs and six-family
all-order within caps are retained. Qualification and source review remain required. -/
set_option autoImplicit false
set_option Elab.async false
set_option stderrAsMessages false
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualFullEGainedAssembly
open EnergyBridge ConnectionError SphereHarmonic NativeThreeHalfCoefficientMultiplier
  NativeCoefficientBoundaryMultiplier NativeOrderOneCoefficientMultiplier ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualJacobiAngularGainedRows ActualPiJacobiRadialGainedRows
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "Pphys" => ℝ × (R3 × ℝ)
local notation "Tpar" => Pphys × (R3 →L[ℝ] ℝ)
local notation "PP" => sphereSobolevDualPairing (1/2 : ℝ)
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete

namespace EndpointLiteralConversion

universe u v

open Lean Meta Elab Tactic

private def sourceSection {f : R3 → SphereL2} (_h : ContDiff ℝ ∞ f) :
    R3 → SphereL2 := f

private theorem lambda_heq_same {α : Sort u} {β γ : α → Sort v}
    {f : (x : α) → β x} {g : (x : α) → γ x}
    (hβ : β = γ) (h : ∀ x, HEq (f x) (g x)) : HEq f g := by
  cases hβ
  apply heq_of_eq
  apply funext
  intro x
  exact eq_of_heq (h x)

private theorem forall_eq_same {α : Sort u} {β γ : α → Sort v}
    (hβ : β = γ) : ((x : α) → β x) = ((x : α) → γ x) := by
  cases hβ
  rfl


/-- Heterogeneous extensionality with an actually proved domain equality. -/
private theorem lambda_heq {α α' : Sort u} {β : α → Sort v} {γ : α' → Sort v}
    {f : (x : α) → β x} {g : (y : α') → γ y}
    (hα : α = α') (h : ∀ x y, HEq x y → HEq (f x) (g y)) : HEq f g := by
  subst hα
  have hβ : β = γ := by
    funext x
    exact type_eq_of_heq (h x x (HEq.refl x))
  subst hβ
  apply heq_of_eq
  apply funext
  intro x
  exact eq_of_heq (h x x (HEq.refl x))

/-- Dependent forall transport preserves the complete codomain family. -/
private theorem forall_eq {α α' : Sort u} {β : α → Sort v} {γ : α' → Sort v}
    (hα : α = α') (hβ : HEq β γ) :
    ((x : α) → β x) = ((y : α') → γ y) := by
  subst hα
  have hβ' : β = γ := eq_of_heq hβ
  subst hβ'
  rfl

/-- Application congruence for related bound function variables. -/
private theorem application_heq {α α' : Sort u} {β : α → Sort v} {γ : α' → Sort v}
    {f : (x : α) → β x} {g : (y : α') → γ y} {x : α} {y : α'}
    (hα : α = α') (hβ : HEq β γ) (hf : HEq f g) (hx : HEq x y) :
    HEq (f x) (g y) := by
  subst hα
  have hβ' : β = γ := eq_of_heq hβ
  subst hβ'
  have hf' : f = g := eq_of_heq hf
  subst hf'
  have hx' : x = y := eq_of_heq hx
  subst hx'
  rfl

private structure BuildState where
  proofs : Std.HashMap (Expr × Expr) Expr := {}
  congrs : Std.HashMap (Expr × Nat) CongrTheorem := {}

private abbrev BuildM := StateRefT BuildState MetaM

/-- Only local substitution, beta reduction and public primitive projections.
No environment mathematical definition is unfolded. -/
private partial def expose (e : Expr) : MetaM Expr := do
  let e ← instantiateMVars e
  match e with
  | .mdata _ b => expose b
  | .letE _ _ value body _ => expose (body.instantiate1 value)
  | .fvar id =>
      match (← id.getDecl).value? with
      | some value => expose value
      | none => pure e
  | .proj n i major =>
      let majorType ← inferType major
      let .const n' us := majorType.getAppFn
        | throwError "literal conversion: unsupported projection type"
      unless n == n' do
        throwError "literal conversion: projection type head mismatch"
      let some info := getStructureInfo? (← getEnv) n
        | throwError "literal conversion: missing public projection information"
      let some projection := info.getProjFn? i
        | throwError "literal conversion: missing public projection function"
      pure (mkApp (mkAppN (mkConst projection us) majorType.getAppArgs) major)
  | .app .. =>
      let head := e.getAppFn
      let args := e.getAppArgs
      if head.isConstOf ``sourceSection then
        unless args.size == 2 do
          throwError "literal conversion: unexpected extraction wrapper arity"
        return ← expose args[0]!
      let head' ← expose head
      if head' != head || head'.isLambda then
        return ← expose (mkAppN head' args).headBeta
      pure e
  | _ => pure e

private def eqFromHEq (site : String) (h : Expr) : MetaM Expr := do
  try
    mkEqOfHEq h (check := true)
  catch _ =>
    throwError "literal conversion: checked HEq-to-Eq conversion failed at {site}"

/-- Actual structural congruence, with proof irrelevance restricted to proofs. -/
private partial def build (a b : Expr) : BuildM Expr := do
  -- Preserve identical public expressions before exposing local lets/projections.
  if a == b then return ← mkHEqRefl a
  if let some h := (← get).proofs[(a,b)]? then return h
  let a' ← expose a
  let b' ← expose b
  let h ← go a' b'
  modify fun s => { s with proofs := s.proofs.insert (a,b) h }
  return h
where
  go (a b : Expr) : BuildM Expr := do
    if a == b then return ← mkHEqRefl a
    let aType ← inferType a
    let bType ← inferType b
    if (← isProp aType) && (← isProp bType) then
      return mkApp4 (mkConst ``proof_irrel_heq) aType bType a b
    let dataClasses : List Name := [``NormedSpace, ``NormedField, ``NontriviallyNormedField,
      ``NormedAddCommGroup, ``SeminormedAddCommGroup]
    if dataClasses.contains (aType.getAppFn.constName?.getD `not_a_data_class) then
      unless (← withTransparency .all (isDefEq a b)) do
        throwError "endpoint literal conversion: unequal canonical normed data"
      return ← mkHEqRefl a
    match a, b with
    | .lam name domain body bi, .lam name' domain' body' bi' =>
        if domain == domain' then
          withLocalDecl name bi domain fun x => do
            let ax := body.instantiate1 x
            let bx := body'.instantiate1 x
            let pointwise ← build ax bx
            let aCodomain ← inferType ax
            let bCodomain ← inferType bx
            let beta ← mkLambdaFVars #[x] aCodomain
            let gamma ← mkLambdaFVars #[x] bCodomain
            let codomainHEq ← build beta gamma
            let codomainEq ← eqFromHEq "same-domain lambda codomain" codomainHEq
            let pointwise ← mkLambdaFVars #[x] pointwise
            let u ← getLevel domain
            let v ← getLevel aCodomain
            unless v == (← getLevel bCodomain) do
              throwError "literal conversion: unequal lambda codomain levels"
            pure (mkAppN (mkConst ``lambda_heq_same [u,v])
              #[domain,beta,gamma,a,b,codomainEq,pointwise])
        else
          let domainHEq ← build domain domain'
          let domainEq ← eqFromHEq "unequal-domain lambda domain" domainHEq
          let u ← getLevel domain
          unless u == (← getLevel domain') do
            throwError "literal conversion: unequal lambda domain levels"
          withLocalDecl name bi domain fun x =>
          withLocalDecl name' bi' domain' fun y => do
            let relation ← mkHEq x y
            withLocalDeclD `literal_bound_heq relation fun hxy => do
              modify fun st => { st with proofs := st.proofs.insert (x,y) hxy }
              let ax := body.instantiate1 x
              let bx := body'.instantiate1 y
              let pointwise ← build ax bx
              let aCodomain ← inferType ax
              let bCodomain ← inferType bx
              let beta ← mkLambdaFVars #[x] aCodomain
              let gamma ← mkLambdaFVars #[y] bCodomain
              let pointwise ← mkLambdaFVars #[x,y,hxy] pointwise
              let v ← getLevel aCodomain
              unless v == (← getLevel bCodomain) do
                throwError "literal conversion: unequal lambda codomain levels"
              pure (mkAppN (mkConst ``lambda_heq [u,v])
                #[domain,domain',beta,gamma,a,b,domainEq,pointwise])
    | .forallE name domain body bi, .forallE name' domain' body' bi' =>
        if domain == domain' then
          withLocalDecl name bi domain fun x => do
            let ax := body.instantiate1 x
            let bx := body'.instantiate1 x
            let beta ← mkLambdaFVars #[x] ax
            let gamma ← mkLambdaFVars #[x] bx
            let familyHEq ← build beta gamma
            let familyEq ← eqFromHEq "same-domain forall family" familyHEq
            let u ← getLevel domain
            let v ← getLevel ax
            unless v == (← getLevel bx) do
              throwError "literal conversion: unequal forall codomain levels"
            mkHEqOfEq (mkAppN (mkConst ``forall_eq_same [u,v])
              #[domain,beta,gamma,familyEq])
        else
          let domainHEq ← build domain domain'
          let domainEq ← eqFromHEq "unequal-domain forall domain" domainHEq
          let u ← getLevel domain
          unless u == (← getLevel domain') do
            throwError "literal conversion: unequal forall domain levels"
          let beta := Expr.lam name domain body bi
          let gamma := Expr.lam name' domain' body' bi'
          let familyHEq ← build beta gamma
          withLocalDecl name bi domain fun x =>
          withLocalDecl name' bi' domain' fun y => do
            let v ← getLevel (body.instantiate1 x)
            unless v == (← getLevel (body'.instantiate1 y)) do
              throwError "literal conversion: unequal forall codomain levels"
            mkHEqOfEq (mkAppN (mkConst ``forall_eq [u,v])
              #[domain,domain',beta,gamma,domainEq,familyHEq])
    | .app .., .app .. =>
        let head := a.getAppFn
        let args := a.getAppArgs
        let args' := b.getAppArgs
        unless head == b.getAppFn && args.size == args'.size do
          let .app fa xa := a
            | throwError "literal conversion: source application expected"
          let .app fb xb := b
            | throwError "literal conversion: target application expected"
          let functionsHEq ← build fa fb
          let faType ← expose (← inferType fa)
          let fbType ← expose (← inferType fb)
          let .forallE na da ba bia := faType
            | throwError "literal conversion: source public function type expected"
          let .forallE nb db bb bib := fbType
            | throwError "literal conversion: target public function type expected"
          let domainHEq ← build da db
          let domainEq ← eqFromHEq "application domain" domainHEq
          let beta := Expr.lam na da ba bia
          let gamma := Expr.lam nb db bb bib
          let familyHEq ← build beta gamma
          let argumentHEq ← build xa xb
          let u ← getLevel da
          let v ← getLevel aType
          unless u == (← getLevel db) && v == (← getLevel bType) do
            throwError "literal conversion: unequal application universe levels"
          return mkAppN (mkConst ``application_heq [u,v])
            #[da,db,beta,gamma,fa,fb,xa,xb,domainEq,familyHEq,functionsHEq,argumentHEq]
        let key := (head,args.size)
        let congr ← match (← get).congrs[key]? with
          | some congr => pure congr
          | none => do
              let congr ← mkHCongrWithArity head args.size
              modify fun s => { s with congrs := s.congrs.insert key congr }
              pure congr
        let mut result := congr.proof
        for i in [:args.size] do
          let h ← build args[i]! args'[i]!
          let h ← match congr.argKinds[i]! with
            | .eq => eqFromHEq "hcongr equality argument" h
            | .heq => pure h
            | _ => throwError "literal conversion: unsupported hcongr argument kind"
          result := mkApp3 result args[i]! args'[i]! h
        pure result
    | _, _ => throwError "literal conversion: unsupported nonidentical data"

elab "endpoint_literal_function_eq" : tactic => withMainContext do
  let goal ← getMainGoal
  let target ← goal.getType
  let some (_, lhs, rhs) := target.eq?
    | throwError "literal conversion: function equality goal expected"
  let h ← (build lhs rhs).run' {}
  let h ← eqFromHEq "literal function result" h
  goal.assign h
  replaceMainGoal []

elab "endpoint_literal_transport " h:term : tactic => withMainContext do
  let goal ← getMainGoal
  let target ← goal.getType
  let sourceProof ← Term.elabTerm h none
  let sourceProof ← instantiateMVars sourceProof
  let source ← inferType sourceProof
  unless (← isProp source) && (← isProp target) do
    throwError "endpoint literal conversion: proposition transport expected"
  let graphHEq ← (build source target).run' {}
  let graphEq ← eqFromHEq "graph proposition result" graphHEq
  let proof := mkApp4 (mkConst ``Eq.mp [Level.zero]) source target graphEq sourceProof
  goal.assign proof
  replaceMainGoal []

end EndpointLiteralConversion

section Algebra
variable {E F N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedAddCommGroup N] [NormedSpace ℝ N]

end Algebra

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics)
  (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
variable (Room : ReferenceGaugeNormalReciprocalRoom g L Φ a
  (Icc (0 : ℝ) 1 ×ˢ (closedBall y0 ρ ×ˢ Icc (-ρ) ρ)))
local notation "CoeffRoom" => CoefficientGermRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ParamRoom" δ:max => Set.prod (commonRoom y0 ρ δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "EH" => canonicalHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "EL" => canonicalLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ZH" => zeroCorrectionHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ZL" => zeroCorrectionHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "zH" => zeroReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "zL" => zeroReverseHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Rh" => originalRadialHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Rl" => originalRadialLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "sh" => originalRadialReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "sl" => originalRadialReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Hh" => jacobiAngularOperatorHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Hl" => jacobiAngularOperatorLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "hh" => jacobiAngularReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "hl" => jacobiAngularReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "RR" => retainedAdjacentHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room
local notation "RH" => radialAngularHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "HR" => angularRadialHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "HH" => jacobiAngularHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Ω" => referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
local notation "PiL" => referencePiHalfMultiplier g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "PiN" => referencePiNegativeHalfMultiplier g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

attribute [local irreducible] canonicalHigh canonicalLow orderedReverseHigh orderedReverseLow
  originalRadialHigh originalRadialLow originalRadialReverseHigh originalRadialReverseLow
  jacobiAngularOperatorHigh jacobiAngularOperatorLow jacobiAngularReverseHigh jacobiAngularReverseLow
  zeroCorrectionHigh zeroCorrectionHalf zeroReverseHigh zeroReverseHalf sphereSobolevInclusionL
  nativeThreeHalfCoefficientMulL nativeHalfCoefficientMulL nativeNegativeHalfCoefficientMulL
  fullGainedHigh retainedAdjacentHigh radialAngularHigh angularRadialHigh jacobiAngularHigh
  commonRoom referenceRadialEndpointInvertibleLocus

set_option Elab.async true in
theorem exists_commonRoom_actual_fullE_gained_smooth_endpoints
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ ρ ∧
    ∃ W : CoeffRoom δ0,
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ0 ∧ δ ≤ ρ ∧ commonRoom y0 ρ δ ⊆ Ω ∧
    ∃ Gcoord : Fin 3 → Pphys → Half →L[ℝ] Half,
    ∃ GN : Fin 3 → Fin 3 → Pphys → Half →L[ℝ] Half,
    ∃ Cl : Fin 3 → Fin 3 → Tpar → Half →L[ℝ] Neg,
      (∀ i j : Fin 3,
        ContDiffOn ℝ ∞ (fullGainedHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg Gcoord GN δ0 W i j) (ParamRoom δ) ∧
        ContDiffOn ℝ ∞ (Cl i j) (ParamRoom δ)) ∧
      (∀ i : Fin 3, ContDiffOn ℝ ∞ (EH i) (ParamRoom δ) ∧
        ContDiffOn ℝ ∞ (EL i) (ParamRoom δ) ∧
        ContDiffOn ℝ ∞ (orderedReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i) (ParamRoom δ) ∧
        ContDiffOn ℝ ∞ (orderedReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i) (ParamRoom δ)) ∧
      (∀ i j : Fin 3, ∀ t ∈ ParamRoom δ, ∀ u : Hi,
        JL (fullGainedHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg Gcoord GN δ0 W i j t u) =
          orderedReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i t (EH j t u)-
            EL j t (orderedReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i t u)) ∧
      (∀ i j : Fin 3, ∀ t ∈ ParamRoom δ,
        (Cl i j t).comp IH=(JL).comp (fullGainedHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg Gcoord GN δ0 W i j t) ∧
        (sphereSobolevInclusionL (-(1/2 : ℝ)) (-(3/2 : ℝ)) (by norm_num)).comp (Cl i j t)=
          (v016TransposeL (fullGainedHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg Gcoord GN δ0 W j i t)).comp JL ∧
        ‖Cl i j t‖ ≤
          (‖fullGainedHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg Gcoord GN δ0 W j i t‖+
           ‖fullGainedHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg Gcoord GN δ0 W i j t‖)/2) ∧
      (∀ N : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ i j : Fin 3, ∀ n : ℕ, n ≤ N → ∀ t ∈ ParamRoom δ,
        ‖iteratedFDerivWithin ℝ n
          (fullGainedHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg Gcoord GN δ0 W i j) (ParamRoom δ) t‖ ≤ M ∧
        ‖iteratedFDerivWithin ℝ n (Cl i j) (ParamRoom δ) t‖ ≤ M ∧
        ‖iteratedFDerivWithin ℝ n (EH i) (ParamRoom δ) t‖ ≤ M ∧
        ‖iteratedFDerivWithin ℝ n (EL i) (ParamRoom δ) t‖ ≤ M ∧
        ‖iteratedFDerivWithin ℝ n
          (orderedReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i) (ParamRoom δ) t‖ ≤ M ∧
        ‖iteratedFDerivWithin ℝ n
          (orderedReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i) (ParamRoom δ) t‖ ≤ M) := by
  classical
  run_tac do
    let out ← IO.getStderr
    out.putStrLn "E-JOINT BODY-ENTER"
    out.flush
  let ordinaryWitnesses := exists_ordinary_smooth_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg
  let δ0 : ℝ := Classical.choose ordinaryWitnesses
  have ordinaryFacts := Classical.choose_spec ordinaryWitnesses
  have hδ0 : 0 < δ0 := ordinaryFacts.1
  have hδ0ρ : δ0 ≤ ρ := ordinaryFacts.2.1
  let W : CoeffRoom δ0 := Classical.choose ordinaryFacts.2.2
  have ordinaryFields := Classical.choose_spec ordinaryFacts.2.2
  have hOrdAt := ordinaryFields.1
  have hZeroAt := ordinaryFields.2
  run_tac do
    let out ← IO.getStderr
    out.putStrLn "E-JOINT ORDINARY-SELECTED"
    out.flush
  let hhWitnesses := hhHigh_smooth_graph_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg hKernel δ0 hδ0 W
  let dH : ℝ := Classical.choose hhWitnesses
  have hhFacts := Classical.choose_spec hhWitnesses
  have hdH : 0 < dH := hhFacts.1
  have hHSm := hhFacts.2.2.2.1
  have hHGraph := hhFacts.2.2.2.2
  run_tac do
    let out ← IO.getStderr
    out.putStrLn "E-JOINT HH-SELECTED"
    out.flush
  let rrWitnesses := rrHigh_smooth_graph_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg hKernel δ0 hδ0 W
  let dR : ℝ := Classical.choose rrWitnesses
  have rrFacts := Classical.choose_spec rrWitnesses
  have hdR : 0 < dR := rrFacts.1
  have hdRρ : dR ≤ ρ := rrFacts.2.2.1
  have hRSm := rrFacts.2.2.2.1
  have hRGraph := rrFacts.2.2.2.2
  run_tac do
    let out ← IO.getStderr
    out.putStrLn "E-JOINT RR-SELECTED"
    out.flush
  let mixedWitnesses := exists_commonRoom_actualPiJacobi_mixed_high_graphs_and_smooth
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg hKernel δ0 hδ0 W
  let dM : ℝ := Classical.choose mixedWitnesses
  have mixedFacts := Classical.choose_spec mixedWitnesses
  have hdM : 0 < dM := mixedFacts.1
  have hRoomM : commonRoom y0 ρ dM ⊆ Ω := mixedFacts.2.2.2.1
  let Gcoord := Classical.choose mixedFacts.2.2.2.2
  have coordFacts := Classical.choose_spec mixedFacts.2.2.2.2
  let GN := Classical.choose coordFacts
  have gainFacts := Classical.choose_spec coordFacts
  have hMSm := gainFacts.1
  have hRHGraph := gainFacts.2.1
  have hHRGraph := gainFacts.2.2
  run_tac do
    let out ← IO.getStderr
    out.putStrLn "E-JOINT PRODUCERS-DONE"
    out.flush
  let δ := min δ0 (min dH (min dR dM))
  have hδ : 0 < δ := lt_min hδ0 (lt_min hdH (lt_min hdR hdM))
  have hδ0le : δ ≤ δ0 := min_le_left _ _
  have hδH : δ ≤ dH := (min_le_right _ _).trans (min_le_left _ _)
  have hδR : δ ≤ dR := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδM : δ ≤ dM := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hSub0 := commonRoom_mono y0 ρ hδ0le
  have hSubH := commonRoom_mono y0 ρ hδH
  have hSubR := commonRoom_mono y0 ρ hδR
  have hSubM := commonRoom_mono y0 ρ hδM
  have hPSub0 : ParamRoom δ ⊆ ParamRoom δ0 := fun t ht => ⟨hSub0 ht.1,ht.2⟩
  have hPSubR : ParamRoom δ ⊆ ParamRoom dR := fun t ht => ⟨hSubR ht.1,ht.2⟩
  have hPSubM : ParamRoom δ ⊆ ParamRoom dM := fun t ht => ⟨hSubM ht.1,ht.2⟩
  have hRoom : commonRoom y0 ρ δ ⊆ Ω := hSubM.trans hRoomM
  let Ch := fullGainedHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room hreg Gcoord GN δ0 W
  let eH := orderedReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
  let eL := orderedReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
  have hOrdSm (i : Fin 3) : ContDiffOn ℝ ∞ (EH i) (ParamRoom δ) ∧
      ContDiffOn ℝ ∞ (EL i) (ParamRoom δ) ∧
      ContDiffOn ℝ ∞ (eH i) (ParamRoom δ) ∧ ContDiffOn ℝ ∞ (eL i) (ParamRoom δ) := by
    exact ⟨fun t ht => (hOrdAt i t (hPSub0 ht)).1.contDiffWithinAt,
      fun t ht => (hOrdAt i t (hPSub0 ht)).2.1.contDiffWithinAt,
      fun t ht => (hOrdAt i t (hPSub0 ht)).2.2.1.contDiffWithinAt,
      fun t ht => (hOrdAt i t (hPSub0 ht)).2.2.2.contDiffWithinAt⟩
  run_tac do
    let out ← IO.getStderr
    out.putStrLn "E-JOINT ORDINARY-DONE"
    out.flush
  have hFullSm (i j : Fin 3) : ContDiffOn ℝ ∞ (Ch i j) (ParamRoom δ) := by
    have hRR := (hRSm i j).mono hPSubR
    have hRH := ((hMSm i j).1).mono hPSubM
    have hHR := ((hMSm i j).2).mono hPSubM
    have hHH : ContDiffOn ℝ ∞ (fun t : Tpar => HH δ0 W i j t.1) (ParamRoom δ) :=
      (hHSm i j).comp contDiffOn_fst (fun t ht => hSubH ht.1)
    have hZero : ContDiffOn ℝ ∞
        (zeroReverseEHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 i j) (ParamRoom δ) :=
      fun t ht => (hZeroAt i j t (hPSub0 ht)).contDiffWithinAt
    have hKZ := complementaryZeroRow_contDiffOn g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg δ0 W δ hSub0 hRoom i j
    have hSmooth := ((((hRR.add hRH).add hHR).add hHH).add hZero).add hKZ
    exact hSmooth.congr (f₁ := Ch i j) (fun z _ => by
      unfold Ch fullGainedHigh
      rfl)
  run_tac do
    let out ← IO.getStderr
    out.putStrLn "E-JOINT SMOOTH-DONE"
    out.flush
  have hGraph (i j : Fin 3) (t : Tpar) (ht : t ∈ ParamRoom δ) (u : Hi) :
      JL (Ch i j t u)=eL i t (EH j t u)-EL j t (eH i t u) := by
    have hSeg := segment_of_mem_commonRoom hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hRoom t.1 ht.1
    exact fullGainedHigh_graph_of_actual_bands g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room
      hreg Gcoord GN δ0 W i j t (hPSub0 ht) hSeg
      (hRGraph i j t (hPSubR ht))
      (hRHGraph i j t (hPSubM ht)) (hHRGraph i j t (hPSubM ht))
      (hHGraph i j t.1 (hSubH ht.1)) u
  run_tac do
    let out ← IO.getStderr
    out.putStrLn "E-JOINT GRAPH-DONE"
    out.flush
  have hAdj (i j : Fin 3) (t : Tpar) (ht : t ∈ ParamRoom δ) (u v : Hi) :
      PP (IH v) (JL (Ch i j t u))=PP (IH u) (JL (Ch j i t v)) := by
    have hSeg := segment_of_mem_commonRoom hcalc hF hO hD τ0 g L y0 Φ B ε C ρ H a w hData hRoom t.1 ht.1
    exact full_gained_swapped_pairing g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 Room
      hreg Gcoord GN δ0 W i j t (hPSub0 ht) hSeg (fun k l => hGraph k l t ht) u v
  run_tac do
    let out ← IO.getStderr
    out.putStrLn "E-JOINT PAIRING-DONE"
    out.flush
  have hK : IsCompact (ParamRoom δ) := (isCompact_commonRoom y0 ρ δ).prod (isCompact_closedBall _ _)
  have hU : UniqueDiffOn ℝ (ParamRoom δ) :=
    (uniqueDiffOn_commonRoom y0 ρ hData.1.2.1 hδ).prod
      (uniqueDiffOn_convex (convex_closedBall _ _)
        ⟨0,ball_subset_interior_closedBall (mem_ball_self one_pos)⟩)
  have hLow (i j : Fin 3) : ∃ Cl : Tpar → Half →L[ℝ] Neg,
      ContDiffOn ℝ ∞ Cl (ParamRoom δ) ∧ ∀ t ∈ ParamRoom δ,
        (Cl t).comp IH=(JL).comp (Ch i j t) ∧
        (sphereSobolevInclusionL (-(1/2 : ℝ)) (-(3/2 : ℝ)) (by norm_num)).comp (Cl t)=
          (v016TransposeL (Ch j i t)).comp JL ∧
        ‖Cl t‖ ≤ (‖v016TransposeL (Ch j i t)‖+‖Ch i j t‖)/2 ∧
        ‖Cl t‖ ≤ (‖Ch j i t‖+‖Ch i j t‖)/2 :=
    v016_exists_contDiffOn_lowEndpoint (ParamRoom δ) hU
      (Ch i j) (Ch j i) (hFullSm i j) (hFullSm j i) (hAdj i j)
  run_tac do
    let out ← IO.getStderr
    out.putStrLn "E-JOINT LOW-EXISTS-DONE"
    out.flush
  let Cl : Fin 3 → Fin 3 → Tpar → Half →L[ℝ] Neg :=
    fun i j => Classical.choose (hLow i j)
  have hCl (i j : Fin 3) := Classical.choose_spec (hLow i j)
  run_tac do
    let out ← IO.getStderr
    out.putStrLn "E-JOINT LOW-SELECTED"
    out.flush
  refine ⟨δ0,hδ0,hδ0ρ,W,δ,hδ,hδ0le,hδR.trans hdRρ,hRoom,Gcoord,GN,Cl,
    fun i j => ⟨hFullSm i j,(hCl i j).1⟩,hOrdSm,hGraph,?_,?_⟩
  · intro i j t ht
    have hAt := (hCl i j).2 t ht
    exact ⟨hAt.1,hAt.2.1,hAt.2.2.2⟩
  · intro N
    let capResult := exists_uniform_six_family_within_jet_cap
      (X := Tpar) (Y := Hi →L[ℝ] Half) (Z := Half →L[ℝ] Neg)
      (ParamRoom δ) hK hU Ch (fun i (_j : Fin 3) => EH i) (fun i (_j : Fin 3) => eH i)
      Cl (fun i (_j : Fin 3) => EL i) (fun i (_j : Fin 3) => eL i)
      hFullSm (fun i j => (hCl i j).1)
      (fun i _j => (hOrdSm i).1) (fun i _j => (hOrdSm i).2.1)
      (fun i _j => (hOrdSm i).2.2.1) (fun i _j => (hOrdSm i).2.2.2) N
    run_tac do
      let out ← IO.getStderr
      out.putStrLn "E-JOINT GENERIC-CAP-APPLICATION-INFERRED"
      out.flush
    endpoint_literal_transport capResult


end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualFullEGainedAssembly
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualFullEGainedAssembly.exists_commonRoom_actual_fullE_gained_smooth_endpoints
