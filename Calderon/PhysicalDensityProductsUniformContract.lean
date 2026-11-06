import Calderon.PhysicalDensityProductsUniformPointwiseBound
import Calderon.PhysicalDensityProductsProfileProperties
import Mathlib.Tactic
import Calderon.PhysicalProductsCoercivityInterface

set_option Elab.async false

/-!
AUTHOR-PRODUCTS-UNIFORM-CONVERSION-SOURCE-NOV01-v006.
Pre-source expansion SHA256 af8ae6909fa1104d12d2da26c8cf9101e61513c77242a62209594d19e2fc5547.
Uncompiled bounded author candidate; normal kernel/replay/axiom/review checks remain mandatory.

The original uniform Products profile theorem, using exactly the radius and
constant returned by the original pointwise/room producer and the checked
conditional profile interface.
-/

open Set Metric Filter MeasureTheory
open scoped ContDiff Topology InnerProductSpace ENNReal

namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

open EnergyBridge ConnectionError SphereHarmonic NormalCoordinatesFrame
  ActualFiniteHarmonicCore SpectralCoreRegularity SpectralWeightedGraph
  ConformalDepth NormalizedPrincipalMetricSmooth ActualHorizontalNormBridge
  ReferenceDensityBounds ActualFiniteHarmonicModel ReferenceWeightedApproximation


namespace ProductsLiteralConversion

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

elab "products_literal_function_eq" : tactic => withMainContext do
  let goal ← getMainGoal
  let target ← goal.getType
  let some (_, lhs, rhs) := target.eq?
    | throwError "literal conversion: function equality goal expected"
  let h ← (build lhs rhs).run' {}
  let h ← eqFromHEq "literal function result" h
  goal.assign h
  replaceMainGoal []

elab "products_literal_graph_transport " h:term : tactic => withMainContext do
  let goal ← getMainGoal
  let target ← goal.getType
  let sourceProof ← Term.elabTerm h none
  let sourceProof ← instantiateMVars sourceProof
  let source ← inferType sourceProof
  unless source.isAppOfArity ``Eq 3 && target.isAppOfArity ``Eq 3 do
    throwError "literal conversion: only the selected pointwise graph equality is supported"
  let graphHEq ← (build source target).run' {}
  let graphEq ← eqFromHEq "graph proposition result" graphHEq
  let proof := mkApp4 (mkConst ``Eq.mp [Level.zero]) source target graphEq sourceProof
  goal.assign proof
  replaceMainGoal []

end ProductsLiteralConversion

theorem CoercivityTransfer.physical_products_uniform_profile_estimate_of_uniform_profile_bound :
    CoercivityTransfer.physical_products_uniform_profile_estimate := by
  delta CoercivityTransfer.physical_products_uniform_profile_estimate
  intro g g2 hg hg2 L hL y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0
  letI productsOperatorNormedAddCommGroup :
      NormedAddCommGroup (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) :=
    ContinuousLinearMap.toNormedAddCommGroup
      (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (1/2 : ℝ))
      (σ₁₂ := RingHom.id ℝ)
  letI productsOperatorNormedSpace :
      NormedSpace ℝ (SphereSobolev (3/2 : ℝ) →L[ℝ] SphereSobolev (1/2 : ℝ)) :=
    ContinuousLinearMap.toNormedSpace (𝕜' := ℝ)
      (E := SphereSobolev (3/2 : ℝ)) (F := SphereSobolev (1/2 : ℝ))
      (σ₁₂ := RingHom.id ℝ)
  obtain ⟨d, C_P, hd, hdρ, hd1, hCP, hRoom, hW⟩ :=
    exists_products_uniform_pointwise_bound_and_room
      g g2 hg hg2 L hL y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0
  refine ⟨d, C_P, hd, hdρ, hd1, hCP, hW, ?_⟩
  have hProfile := products_profile_properties_of_uniform_pointwise_bound
    g g2 hg hg2 L hL y0 Φ B ε C ρ H a w hData hcalc hreg hF hO hD τ0
    d C_P hd hdρ hd1 hCP hRoom hW
  intro q hq delta A p hdelta hdelta1 hA hp eta betaMin heta heta1 hbeta F hFs hBounds
  have hParameters := hProfile q hq delta A p hdelta hdelta1 hA hp eta betaMin heta heta1 hbeta
  have hCore := hParameters F
  have hSupport := hCore hFs
  have hSection := hSupport hBounds
  intro u V
  let V_source : R3 → SphereL2 := ProductsLiteralConversion.sourceSection hSection.1
  have hV : V_source = V := by
    products_literal_function_eq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hV]
    exact hSection.1
  · rw [← hV]
    exact hSection.2.1
  · rw [← hV]
    exact hSection.2.2.1
  · rw [← hV]
    exact hSection.2.2.2.1
  · intro y
    products_literal_graph_transport (hSection.2.2.2.2.1 y)
  · rw [← hV]
    exact hSection.2.2.2.2.2.1
  · rw [← hV]
    exact hSection.2.2.2.2.2.2

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
