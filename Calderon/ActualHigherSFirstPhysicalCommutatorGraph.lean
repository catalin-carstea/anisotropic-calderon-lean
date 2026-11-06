import Calderon.ActualHigherSScalarCommutatorNativeForm
import Calderon.ActualHigherSPhysicalPairing
set_option autoImplicit false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSFirstPhysicalCommutatorGraph
open PrincipalCommutator ReferenceDensityBounds ActualHigherSScalarCommutatorCoefficients
  ActualHigherSScalarCommutatorForm ActualHigherSScalarCommutatorNativeForm
section Generic
variable {E H M N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup H] [NormedSpace ℝ H] [NormedAddCommGroup M] [NormedSpace ℝ M]
  [NormedAddCommGroup N] [NormedSpace ℝ N]

def coordinateFirstAction (B : Fin 3 → R3 → (E →L[ℝ] H)) (u : R3 → E) (x : R3) : H :=
  ∑ l : Fin 3, B l x (directionalFDeriv (coordinateDirection l) u x)

def coordinateSecondAction (a : Fin 3 → Fin 3 → R3 → ℝ) (u : R3 → E) (x : R3) : E :=
  ∑ i : Fin 3, ∑ j : Fin 3, a i j x •
    directionalFDeriv (coordinateDirection i) (directionalFDeriv (coordinateDirection j) u) x

lemma contDiff_coordinateFirstAction (B : Fin 3 → R3 → (E →L[ℝ] H)) (u : R3 → E)
    (K : Set R3) (hK : IsClosed K) (hu : ContDiff ℝ ∞ u) (h0 : ∀ x ∉ K, u x = 0)
    (hB : ∀ l, ∀ x ∈ K, ContDiffAt ℝ ∞ (B l) x) :
    ContDiff ℝ ∞ (coordinateFirstAction B u) := by
  apply ContDiff.sum
  intro l _
  exact contDiff_supported_operator_apply (directionalFDeriv (coordinateDirection l) u) (B l) K hK
    (contDiff_directionalFDeriv _ u hu)
    (fun x hx => directional_eq_zero_off u K hK h0 _ x hx) (hB l)

lemma coordinateFirstAction_eq_zero_off (B : Fin 3 → R3 → (E →L[ℝ] H)) (u : R3 → E)
    (K : Set R3) (hK : IsClosed K) (h0 : ∀ x ∉ K, u x = 0) (x : R3) (hx : x ∉ K) :
    coordinateFirstAction B u x = 0 := by
  have hd (l : Fin 3) := directional_eq_zero_off u K hK h0 (coordinateDirection l) x hx
  simp only [coordinateFirstAction,hd,map_zero,Finset.sum_const_zero]

/-- Whole supported first-order field graph, not a bare coefficient derivative assertion. -/
theorem coordinateFirstAction_transfer
    (I : E →L[ℝ] M) (J : H →L[ℝ] N)
    (BH : Fin 3 → R3 → (E →L[ℝ] H)) (BL : Fin 3 → R3 → (M →L[ℝ] N))
    (u : R3 → E) (K : Set R3) (hK : IsClosed K) (hu : ContDiff ℝ ∞ u)
    (h0 : ∀ x ∉ K, u x = 0)
    (hGraph : ∀ l, ∀ x ∈ K, ∀ v : E, J (BH l x v) = BL l x (I v)) :
    (fun x => J (coordinateFirstAction BH u x)) =
      coordinateFirstAction BL (fun x => I (u x)) := by
  funext x
  unfold coordinateFirstAction
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro l _
  have hD : directionalFDeriv (coordinateDirection l) (fun y => I (u y)) x =
      I (directionalFDeriv (coordinateDirection l) u x) := by
    have h := directionalFDeriv_clm_apply (coordinateDirection l) (fun _ : R3 => I) u contDiff_const hu x
    simpa only [directionalFDeriv,fderiv_const_apply,zero_apply,map_zero,zero_add] using h
  rw [hD]
  by_cases hx : x ∈ K
  · exact hGraph l x hx _
  · have hz := directional_eq_zero_off u K hK h0 (coordinateDirection l) x hx
    simp only [hz,map_zero]

lemma directional_linear_input (I : E →L[ℝ] M) (u : R3 → E)
    (hu : ContDiff ℝ ∞ u) (X x : R3) :
    directionalFDeriv X (fun y => I (u y)) x = I (directionalFDeriv X u x) := by
  have h := directionalFDeriv_clm_apply X (fun _ : R3 => I) u contDiff_const hu x
  simpa only [directionalFDeriv,fderiv_const_apply,zero_apply,map_zero,zero_add] using h

lemma directional_second_linear_input (I : E →L[ℝ] M) (u : R3 → E)
    (hu : ContDiff ℝ ∞ u) (X Y x : R3) :
    directionalFDeriv X (directionalFDeriv Y (fun y => I (u y))) x =
      I (directionalFDeriv X (directionalFDeriv Y u) x) := by
  have heq : directionalFDeriv Y (fun y => I (u y)) =
      fun y => I (directionalFDeriv Y u y) := funext (directional_linear_input I u hu Y)
  rw [heq]
  exact directional_linear_input I (directionalFDeriv Y u) (contDiff_directionalFDeriv Y u hu) X x

lemma contDiff_coordinateSecondAction (a : Fin 3 → Fin 3 → R3 → ℝ) (u : R3 → E)
    (ha : ∀ i j, ContDiff ℝ ∞ (a i j)) (hu : ContDiff ℝ ∞ u) :
    ContDiff ℝ ∞ (coordinateSecondAction a u) := by
  apply ContDiff.sum
  intro i _
  apply ContDiff.sum
  intro j _
  exact (ha i j).smul (contDiff_directionalFDeriv _ _ (contDiff_directionalFDeriv _ u hu))

lemma coordinateSecondAction_eq_zero_off (a : Fin 3 → Fin 3 → R3 → ℝ) (u : R3 → E)
    (K : Set R3) (hK : IsClosed K) (h0 : ∀ x ∉ K, u x = 0) (x : R3) (hx : x ∉ K) :
    coordinateSecondAction a u x = 0 := by
  have hd0 (j : Fin 3) : ∀ y ∉ K, directionalFDeriv (coordinateDirection j) u y = 0 :=
    fun y hy => directional_eq_zero_off u K hK h0 (coordinateDirection j) y hy
  have hdd (i j : Fin 3) := directional_eq_zero_off (directionalFDeriv (coordinateDirection j) u)
    K hK (hd0 j) (coordinateDirection i) x hx
  simp only [coordinateSecondAction,hdd,smul_zero,Finset.sum_const_zero]

lemma coordinateSecondAction_transfer (I : E →L[ℝ] M) (a : Fin 3 → Fin 3 → R3 → ℝ)
    (u : R3 → E) (hu : ContDiff ℝ ∞ u) :
    (fun x => I (coordinateSecondAction a u x)) = coordinateSecondAction a (fun x => I (u x)) := by
  funext x
  unfold coordinateSecondAction
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_smul,directional_second_linear_input I u hu (coordinateDirection i) (coordinateDirection j) x]

/-- Actual composed first/second operators, whose output space need not be a finite harmonic space. -/
def coordinateCommutator (a : Fin 3 → Fin 3 → R3 → ℝ)
    (B : Fin 3 → R3 → (E →L[ℝ] H)) (u : R3 → E) (x : R3) : H :=
  coordinateFirstAction B (coordinateSecondAction a u) x-
    coordinateSecondAction a (coordinateFirstAction B u) x

/-- Full whole-field graph of the composed commutator, by differentiating genuine global field identities. -/
theorem coordinateCommutator_transfer
    (I : E →L[ℝ] M) (J : H →L[ℝ] N)
    (BH : Fin 3 → R3 → (E →L[ℝ] H)) (BL : Fin 3 → R3 → (M →L[ℝ] N))
    (a : Fin 3 → Fin 3 → R3 → ℝ) (u : R3 → E) (K : Set R3) (hK : IsClosed K)
    (hu : ContDiff ℝ ∞ u) (h0 : ∀ x ∉ K, u x = 0)
    (ha : ∀ i j, ContDiff ℝ ∞ (a i j))
    (hBH : ∀ l, ∀ x ∈ K, ContDiffAt ℝ ∞ (BH l) x)
    (hGraph : ∀ l, ∀ x ∈ K, ∀ v : E, J (BH l x v) = BL l x (I v)) :
    (fun x => J (coordinateCommutator a BH u x)) =
      coordinateCommutator a BL (fun x => I (u x)) := by
  have hF := coordinateFirstAction_transfer I J BH BL u K hK hu h0 hGraph
  have hAc := contDiff_coordinateSecondAction a u ha hu
  have hA0 : ∀ x ∉ K, coordinateSecondAction a u x = 0 :=
    fun x hx => coordinateSecondAction_eq_zero_off a u K hK h0 x hx
  have hFA := coordinateFirstAction_transfer I J BH BL (coordinateSecondAction a u) K hK hAc hA0 hGraph
  have hAI := coordinateSecondAction_transfer I a u hu
  have hT1 : (fun x => J (coordinateFirstAction BH (coordinateSecondAction a u) x)) =
      coordinateFirstAction BL (coordinateSecondAction a (fun x => I (u x))) :=
    hFA.trans (congrArg (coordinateFirstAction BL) hAI)
  have hFc := contDiff_coordinateFirstAction BH u K hK hu h0 hBH
  have hAJ := coordinateSecondAction_transfer J a (coordinateFirstAction BH u) hFc
  have hT2 : (fun x => J (coordinateSecondAction a (coordinateFirstAction BH u) x)) =
      coordinateSecondAction a (coordinateFirstAction BL (fun x => I (u x))) :=
    hAJ.trans (congrArg (coordinateSecondAction a) hF)
  funext x
  unfold coordinateCommutator
  rw [map_sub,congrFun hT1 x,congrFun hT2 x]

lemma contDiff_coordinateCommutator (a : Fin 3 → Fin 3 → R3 → ℝ)
    (B : Fin 3 → R3 → (E →L[ℝ] H)) (u : R3 → E) (K : Set R3) (hK : IsClosed K)
    (hu : ContDiff ℝ ∞ u) (h0 : ∀ x ∉ K, u x = 0)
    (ha : ∀ i j, ContDiff ℝ ∞ (a i j))
    (hB : ∀ l, ∀ x ∈ K, ContDiffAt ℝ ∞ (B l) x) :
    ContDiff ℝ ∞ (coordinateCommutator a B u) := by
  have hAu := contDiff_coordinateSecondAction a u ha hu
  have hA0 : ∀ x ∉ K, coordinateSecondAction a u x = 0 :=
    fun x hx => coordinateSecondAction_eq_zero_off a u K hK h0 x hx
  exact (contDiff_coordinateFirstAction B (coordinateSecondAction a u) K hK hAu hA0 hB).sub
    (contDiff_coordinateSecondAction a (coordinateFirstAction B u) ha
      (contDiff_coordinateFirstAction B u K hK hu h0 hB))

lemma coordinateCommutator_eq_zero_off (a : Fin 3 → Fin 3 → R3 → ℝ)
    (B : Fin 3 → R3 → (E →L[ℝ] H)) (u : R3 → E) (K : Set R3) (hK : IsClosed K)
    (h0 : ∀ x ∉ K, u x = 0) (x : R3) (hx : x ∉ K) :
    coordinateCommutator a B u x = 0 := by
  have hA0 : ∀ y ∉ K, coordinateSecondAction a u y = 0 :=
    fun y hy => coordinateSecondAction_eq_zero_off a u K hK h0 y hy
  have hB0 : ∀ y ∉ K, coordinateFirstAction B u y = 0 :=
    fun y hy => coordinateFirstAction_eq_zero_off B u K hK h0 y hy
  exact sub_eq_zero.mpr ((coordinateFirstAction_eq_zero_off B (coordinateSecondAction a u)
    K hK hA0 x hx).trans (coordinateSecondAction_eq_zero_off a (coordinateFirstAction B u)
      K hK hB0 x hx).symm)

lemma directional_fin_sum (f : Fin 3 → R3 → E) (hf : ∀ i, ContDiff ℝ ∞ (f i)) (X x : R3) :
    directionalFDeriv X (fun y => ∑ i : Fin 3, f i y) x =
      ∑ i : Fin 3, directionalFDeriv X (f i) x := by
  unfold directionalFDeriv
  rw [fderiv_fun_sum (fun i (_ : i ∈ (Finset.univ : Finset (Fin 3))) =>
    (hf i).differentiable (by simp) x)]
  simp only [sum_apply]

lemma directional_second_fin_sum (f : Fin 3 → R3 → E) (hf : ∀ i, ContDiff ℝ ∞ (f i))
    (X Y x : R3) :
    directionalFDeriv X (directionalFDeriv Y (fun y => ∑ i : Fin 3, f i y)) x =
      ∑ i : Fin 3, directionalFDeriv X (directionalFDeriv Y (f i)) x := by
  have hEq : directionalFDeriv Y (fun y => ∑ i : Fin 3, f i y) =
      fun y => ∑ i : Fin 3, directionalFDeriv Y (f i) y := funext (directional_fin_sum f hf Y)
  rw [hEq]
  exact directional_fin_sum (fun i => directionalFDeriv Y (f i))
    (fun i => contDiff_directionalFDeriv Y (f i) (hf i)) X x

end Generic
section SumIdentity
variable {E H : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup H] [NormedSpace ℝ H]

/-- Exact identification with the checked coordinate sum, by genuine derivative linearity. -/
theorem coordinateCommutator_eq_coordinate_sum
    (B : Fin 3 → R3 → (E →L[ℝ] H)) (a : Fin 3 → Fin 3 → R3 → ℝ)
    (u : R3 → E) (K : Set R3) (hK : IsClosed K) (hu : ContDiff ℝ ∞ u)
    (h0 : ∀ x ∉ K, u x = 0) (ha : ∀ i j, ContDiff ℝ ∞ (a i j))
    (hB : ∀ l, ∀ x ∈ K, ContDiffAt ℝ ∞ (B l) x) :
    coordinateCommutator a B u = scalarFirstCoordinateCommutatorSum a B u := by
  let f : Fin 3 → Fin 3 → R3 → E := fun i j y =>
    a i j y • directionalFDeriv (coordinateDirection i) (directionalFDeriv (coordinateDirection j) u) y
  let g : Fin 3 → R3 → H := fun l y => B l y (directionalFDeriv (coordinateDirection l) u y)
  have hf (i j : Fin 3) : ContDiff ℝ ∞ (f i j) :=
    (ha i j).smul (contDiff_directionalFDeriv _ _ (contDiff_directionalFDeriv _ u hu))
  have hfr (i : Fin 3) : ContDiff ℝ ∞ (fun y => ∑ j : Fin 3, f i j y) :=
    ContDiff.sum (fun j _ => hf i j)
  have hg (l : Fin 3) : ContDiff ℝ ∞ (g l) :=
    contDiff_supported_operator_apply (directionalFDeriv (coordinateDirection l) u) (B l) K hK
      (contDiff_directionalFDeriv _ u hu)
      (fun x hx => directional_eq_zero_off u K hK h0 _ x hx) (hB l)
  have hAf : coordinateSecondAction a u = fun y => ∑ i : Fin 3, ∑ j : Fin 3, f i j y := rfl
  have hBg : coordinateFirstAction B u = fun y => ∑ l : Fin 3, g l y := rfl
  have hFirst (l : Fin 3) (x : R3) : directionalFDeriv (coordinateDirection l) (coordinateSecondAction a u) x =
      ∑ i : Fin 3, ∑ j : Fin 3, directionalFDeriv (coordinateDirection l) (f i j) x := by
    rw [hAf,directional_fin_sum _ hfr]
    apply Finset.sum_congr rfl
    intro i _
    exact directional_fin_sum (f i) (hf i) _ x
  have hSecond (i j : Fin 3) (x : R3) :
      directionalFDeriv (coordinateDirection i) (directionalFDeriv (coordinateDirection j) (coordinateFirstAction B u)) x =
      ∑ l : Fin 3, directionalFDeriv (coordinateDirection i) (directionalFDeriv (coordinateDirection j) (g l)) x := by
    rw [hBg]
    exact directional_second_fin_sum g hg _ _ x
  funext x
  let A : Fin 3 → Fin 3 → Fin 3 → H := fun i j l =>
    B l x (directionalFDeriv (coordinateDirection l) (f i j) x)
  let D : Fin 3 → Fin 3 → Fin 3 → H := fun i j l =>
    a i j x • directionalFDeriv (coordinateDirection i) (directionalFDeriv (coordinateDirection j) (g l)) x
  have hPerm : (∑ l : Fin 3, ∑ i : Fin 3, ∑ j : Fin 3, A i j l) =
      ∑ i : Fin 3, ∑ j : Fin 3, ∑ l : Fin 3, A i j l := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
  change (∑ l : Fin 3, B l x (directionalFDeriv (coordinateDirection l) (coordinateSecondAction a u) x))-
    (∑ i : Fin 3, ∑ j : Fin 3, a i j x •
      directionalFDeriv (coordinateDirection i) (directionalFDeriv (coordinateDirection j) (coordinateFirstAction B u)) x) = _
  simp_rw [hFirst,hSecond,map_sum,Finset.smul_sum]
  change (∑ l : Fin 3, ∑ i : Fin 3, ∑ j : Fin 3, A i j l)-
    (∑ i : Fin 3, ∑ j : Fin 3, ∑ l : Fin 3, D i j l) =
    ∑ i : Fin 3, ∑ j : Fin 3, ∑ l : Fin 3, (A i j l-D i j l)
  rw [hPerm]
  simp only [Finset.sum_sub_distrib]
end SumIdentity

private lemma contDiffAt_operatorFactor {D V : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (X : Fin 3 → D → ℝ) (Q : Fin 3 → Fin 3 → D → ℝ) (Op : Fin 3 → D → V) (t : D)
    (hX : ∀ m, ContDiffAt ℝ ∞ (X m) t) (hQ : ∀ i j, ContDiffAt ℝ ∞ (Q i j) t)
    (hOp : ∀ i, ContDiffAt ℝ ∞ (Op i) t) :
    ContDiffAt ℝ ∞ (fun z => ∑ m : Fin 3, X m z •
      ((∑ j : Fin 3, Q m j z • Op j z)+(∑ i : Fin 3, Q i m z • Op i z))) t := by
  apply ContDiffAt.sum
  intro m _
  exact (hX m).smul ((ContDiffAt.sum (fun j _ => (hQ m j).smul (hOp j))).add
    (ContDiffAt.sum (fun i _ => (hQ i m).smul (hOp i))))

section Native
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft ActualScalarPrincipalAdjoint
  ActualFullEGainedEndpoints ActualRetainedGeneratorMultiplierGains SmoothMetricFrame MovingFrameConnection
  ActualFiniteHarmonicCore ActualFiniteHarmonicModel ActualNormalizedSecondMetricDrift
  ConformalDepth ReferenceWeightedApproximation ActualJacobiAngularGainedRows ActualPiJacobiRadialGainedRows
  ActualGeneratorRadialGainedRows ActualCanonicalGeneratorAngularGainedRows NativeThreeHalfCoefficientMultiplier
  NativeCoefficientBoundaryMultiplier NativeOrderOneCoefficientMultiplier ActualGeneratorEHighGainedGraph
  ActualGeneratorEHighSmoothGerms SphereHarmonic.DegreeGraphLifting
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
local notation "Tpar" => (ℝ × (R3 × ℝ)) × (R3 →L[ℝ] ℝ)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete
@[instance_reducible] private def highCoeffNormed : NormedAddCommGroup (Hi →L[ℝ] Half) := inferInstance
attribute [local instance] highCoeffNormed
@[instance_reducible] private def highCoeffSpace : NormedSpace ℝ (Hi →L[ℝ] Half) := inferInstance
attribute [local instance] highCoeffSpace
@[instance_reducible] private def lowCoeffNormed : NormedAddCommGroup (Half →L[ℝ] Neg) := inferInstance
attribute [local instance] lowCoeffNormed
@[instance_reducible] private def lowCoeffSpace : NormedSpace ℝ (Half →L[ℝ] Neg) := inferInstance
attribute [local instance] lowCoeffSpace
@[instance_reducible] private def highParameterNormed : NormedAddCommGroup Tpar := inferInstance
attribute [local instance] highParameterNormed
@[instance_reducible] private def highParameterSpace : NormedSpace ℝ Tpar := inferInstance
attribute [local instance] highParameterSpace
attribute [local irreducible] canonicalHigh referenceDensityPrincipalFrameCoefficient
 ActualBalancedFirstPrincipalError.frameEntry ActualHigherSFormation.higherSParam

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace)
local notation "CoeffRoom" => CoefficientGermRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "CRoom" => ActualCommonFirstWordQuadraticAdjoint.CommonFirstWordRoom
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "EH" => canonicalHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "EL" => canonicalLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "BCC" => ActualHigherSFirstCoefficientJets.canonicalFirstCoordinateCoefficient
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "ParamRoom" δ:max => Set.prod (commonRoom y0 ρ δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "Tq" δr:max Ar:max p:max q:max => ActualHigherSFormation.higherSParam L δr Ar p q

/-- Actual high realization of the same first-coordinate factor, retaining both Q orders. -/
def highFirstCoordinateFactor (g2 : MatrixField) (l : Fin 3) (t : Tpar) : Hi →L[ℝ] Half :=
  ∑ m : Fin 3, ActualBalancedFirstPrincipalError.frameEntry g L m l (t.1.1,t.1.2.1) •
    ((∑ j : Fin 3, referenceDensityPrincipalFrameCoefficient g g2 L t.1.1 t.1.2.1 m j • EH j t)+
      ∑ i : Fin 3, referenceDensityPrincipalFrameCoefficient g g2 L t.1.1 t.1.2.1 i m • EH i t)
local notation "HF" => highFirstCoordinateFactor g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

def highFirstCoordinateCoefficient (g2 : MatrixField) (δr Ar : ℝ) (p : ℕ) (q : ℝ)
    (x : R3) (l : Fin 3) : Hi →L[ℝ] Half :=
  (referenceRadius δr Ar p L x)^2 • HF g2 l ((Tq δr Ar p q) x)
local notation "HCC" => highFirstCoordinateCoefficient g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

lemma contDiffAt_highFirstCoordinateFactor (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0) (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) (l : Fin 3) (t : Tpar)
    (ht : t ∈ ParamRoom δ) : ContDiffAt ℝ ∞ (HF g2 l) t := by
  have hqx : ContDiff ℝ ∞ (fun z : Tpar => (z.1.1,z.1.2.1)) :=
    (contDiff_fst.fst).prodMk (contDiff_fst.snd.fst)
  have hQ (i j : Fin 3) : ContDiff ℝ ∞ (fun z : Tpar =>
      referenceDensityPrincipalFrameCoefficient g g2 L z.1.1 z.1.2.1 i j) :=
    (contDiff_referenceDensityPrincipalFrameCoefficient_joint g g2 hg hg2 L i j).comp hqx
  have hX (m : Fin 3) : ContDiff ℝ ∞ (fun z : Tpar =>
      ActualBalancedFirstPrincipalError.frameEntry g L m l (z.1.1,z.1.2.1)) :=
    (ActualBalancedFirstPrincipalError.contDiff_frameEntry g hg L m l).comp hqx
  exact contDiffAt_operatorFactor
    (fun (m : Fin 3) (z : Tpar) => ActualBalancedFirstPrincipalError.frameEntry g L m l (z.1.1,z.1.2.1))
    (fun (i j : Fin 3) (z : Tpar) => referenceDensityPrincipalFrameCoefficient g g2 L z.1.1 z.1.2.1 i j)
    (fun (j : Fin 3) (z : Tpar) => EH j z) t
    (fun m => (hX m).contDiffAt) (fun i j => (hQ i j).contDiffAt)
    (fun j => Cm.germHigh j t ht)

lemma contDiffAt_highFirstCoordinateCoefficient (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0) (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) (δr Ar : ℝ) (p : ℕ)
    (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ) (l : Fin 3) (x : R3)
    (hx : (Tq δr Ar p q) x ∈ ParamRoom δ) :
    ContDiffAt ℝ ∞ (fun y => HCC g2 δr Ar p q y l) x := by
  have hr := ActualScalarPrincipalAdjoint.contDiff_referenceRadius_actual δr Ar p L hδr hAr
  have ht := ActualHigherSFormation.contDiff_higherSParam hF hO hD g L y0 Φ B ε C ρ H a w
    hData hg hcalc τ0 δr Ar p hδr hAr q
  have hc := (contDiffAt_highFirstCoordinateFactor g L y0 Φ B ε C ρ H a w hData hg hcalc
    hF hO hD τ0 hreg δ0 W δ Cm g2 hg2 l ((Tq δr Ar p q) x) hx).comp x ht.contDiffAt
  exact (hr.contDiffAt.pow 2).smul hc

/-- Exact native high/low coefficient graph, from Cm compatibility; no angular output finiteness. -/
theorem highFirstCoordinateCoefficient_negative_graph (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0) (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (g2 : MatrixField) (δr Ar : ℝ) (p : ℕ) (q : ℝ) (l : Fin 3) (x : R3)
    (hx : (Tq δr Ar p q) x ∈ ParamRoom δ) (v : Hi) :
    JL (HCC g2 δr Ar p q x l v) = BCC g2 δr Ar p q x l (IH v) := by
  have hCompat (j : Fin 3) : JL (EH j ((Tq δr Ar p q) x) v) =
      EL j ((Tq δr Ar p q) x) (IH v) := Cm.compat j _ hx v
  simp only [highFirstCoordinateCoefficient,highFirstCoordinateFactor,
    ActualHigherSFirstCoefficientJets.canonicalFirstCoordinateCoefficient,
    ActualHigherSFirstCoefficientJets.firstCoordinateFactor,
    smul_apply,sum_apply,add_apply,map_smul,map_sum,map_add]
  simp_rw [hCompat]

/-- Genuine Half-valued composed physical first-S/scalar commutator. -/
def nativeFirstPhysicalCommutatorHalf (g2 : MatrixField) (δr Ar : ℝ) (p : ℕ) (q : ℝ)
    (h : MatrixField) (F0 : smoothCompactFiniteSphereCore hO hD) : R3 → Half :=
  coordinateCommutator (fun i j y => actualPrincipalMatrix g L q δr Ar p h y i j)
    (fun l y => HCC g2 δr Ar p q y l) (ActualHigherSFormation.higherSInput hO hD F0)
local notation "PC" => nativeFirstPhysicalCommutatorHalf
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

def nativeFirstPhysicalCommutatorOut (g2 : MatrixField) (δr Ar : ℝ) (p : ℕ) (q : ℝ)
    (h : MatrixField) (F0 : smoothCompactFiniteSphereCore hO hD) : R3 → SphereL2 :=
  fun x => sphereSobolevHalfToSphereL2L hO hD (PC g2 δr Ar p q h F0 x)
local notation "PO" => nativeFirstPhysicalCommutatorOut
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "NC" => nativeScalarFirstCommutator
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

lemma higherSInput_eq_zero_off (F0 : smoothCompactFiniteSphereCore hO hD) (x : R3)
    (hx : x ∉ tsupport F0.val) : ActualHigherSFormation.higherSInput hO hD F0 x = 0 := by
  have hr := finiteCoreSobolevLift_representation hO hD (3/2 : ℝ) (by norm_num) F0
  exact image_eq_zero_of_notMem_tsupport (fun hz => hx (hr.2.2.1 hz))

/-- Full native negative graph; output retains every angular degree. -/
theorem nativeFirstPhysicalCommutator_negative_graph
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) (δr Ar : ℝ) (p : ℕ)
    (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ) (h : MatrixField)
    (hh : ∀ i j, ContDiff ℝ ∞ (fun y => h y i j))
    (F0 : smoothCompactFiniteSphereCore hO hD)
    (hTF : ∀ x ∈ tsupport F0.val, (Tq δr Ar p q) x ∈ ParamRoom δ) :
    (fun x => JL (PC g2 δr Ar p q h F0 x)) = NC g2 δr Ar p q h F0 := by
  let aa : Fin 3 → Fin 3 → R3 → ℝ := fun i j y => actualPrincipalMatrix g L q δr Ar p h y i j
  let bh : Fin 3 → R3 → (Hi →L[ℝ] Half) := fun l y => HCC g2 δr Ar p q y l
  let bl : Fin 3 → R3 → (Half →L[ℝ] Neg) := fun l y => BCC g2 δr Ar p q y l
  let U : R3 → Hi := ActualHigherSFormation.higherSInput hO hD F0
  let K := tsupport F0.val
  have hK : IsClosed K := isClosed_tsupport F0.val
  have hU : ContDiff ℝ ∞ U := contDiff_finiteCoreSobolevLift hO hD (3/2 : ℝ) F0
  have hU0 : ∀ x ∉ K, U x = 0 := higherSInput_eq_zero_off hO hD F0
  have ha : ∀ i j, ContDiff ℝ ∞ (aa i j) :=
    ActualPerturbedDefect.contDiff_actualPrincipalMatrix_entry g hg L q δr Ar p h hδr hAr hh
  have hbh : ∀ l, ∀ x ∈ K, ContDiffAt ℝ ∞ (bh l) x := by
    intro l x hx
    exact contDiffAt_highFirstCoordinateCoefficient g L y0 Φ B ε C ρ H a w hData hg hcalc
      hF hO hD τ0 hreg δ0 W δ Cm g2 hg2 δr Ar p hδr hAr q l x (hTF x hx)
  have hbl : ∀ l, ∀ x ∈ K, ContDiffAt ℝ ∞ (bl l) x := by
    intro l x hx
    exact ActualHigherSFirstCoefficientJets.contDiffAt_canonicalFirstCoordinateCoefficient
      g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm
      g2 hg2 δr Ar p hδr hAr q x (hTF x hx) l
  have hGraph : ∀ l, ∀ x ∈ K, ∀ v : Hi, JL (bh l x v) = bl l x (IH v) := by
    intro l x hx v
    exact highFirstCoordinateCoefficient_negative_graph g L y0 Φ B ε C ρ H a w hData hg hcalc
      hF hO hD τ0 hreg δ0 W δ Cm g2 δr Ar p q l x (hTF x hx) v
  have hglo := coordinateCommutator_transfer IH JL bh bl aa U K hK hU hU0 ha hbh hGraph
  have hI : (fun x => IH (U x)) = halfInput hO hD F0 := rfl
  have hUhalf := contDiff_halfInput hO hD F0
  have h0half := halfInput_eq_zero_off hO hD F0
  have hsum := coordinateCommutator_eq_coordinate_sum bl aa (halfInput hO hD F0) K hK
    hUhalf h0half ha hbl
  have hre : coordinateCommutator aa bl (fun x => IH (U x)) = NC g2 δr Ar p q h F0 := by
    rw [hI,hsum]
    rfl
  exact hglo.trans hre

/-- Native Half commutator has a genuine smooth compactly supported realization. -/
theorem nativeFirstPhysicalCommutator_smooth_compact
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) (δr Ar : ℝ) (p : ℕ)
    (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ) (h : MatrixField)
    (hh : ∀ i j, ContDiff ℝ ∞ (fun y => h y i j))
    (F0 : smoothCompactFiniteSphereCore hO hD)
    (hTF : ∀ x ∈ tsupport F0.val, (Tq δr Ar p q) x ∈ ParamRoom δ) :
    ContDiff ℝ ∞ (PC g2 δr Ar p q h F0) ∧ HasCompactSupport (PC g2 δr Ar p q h F0) := by
  let aa : Fin 3 → Fin 3 → R3 → ℝ := fun i j y => actualPrincipalMatrix g L q δr Ar p h y i j
  let bh : Fin 3 → R3 → (Hi →L[ℝ] Half) := fun l y => HCC g2 δr Ar p q y l
  let U : R3 → Hi := ActualHigherSFormation.higherSInput hO hD F0
  have hU : ContDiff ℝ ∞ U := contDiff_finiteCoreSobolevLift hO hD (3/2 : ℝ) F0
  have hU0 : ∀ x ∉ tsupport F0.val, U x = 0 := higherSInput_eq_zero_off hO hD F0
  have ha : ∀ i j, ContDiff ℝ ∞ (aa i j) :=
    ActualPerturbedDefect.contDiff_actualPrincipalMatrix_entry g hg L q δr Ar p h hδr hAr hh
  have hbh : ∀ l, ∀ x ∈ tsupport F0.val, ContDiffAt ℝ ∞ (bh l) x := by
    intro l x hx
    exact contDiffAt_highFirstCoordinateCoefficient g L y0 Φ B ε C ρ H a w hData hg hcalc
      hF hO hD τ0 hreg δ0 W δ Cm g2 hg2 δr Ar p hδr hAr q l x (hTF x hx)
  have hc := contDiff_coordinateCommutator aa bh U (tsupport F0.val) (isClosed_tsupport F0.val)
    hU hU0 ha hbh
  have hz : ∀ x ∉ tsupport F0.val, coordinateCommutator aa bh U x = 0 :=
    fun x hx => coordinateCommutator_eq_zero_off aa bh U (tsupport F0.val)
      (isClosed_tsupport F0.val) hU0 x hx
  exact ⟨hc,HasCompactSupport.intro F0.property.2.1 hz⟩


/-- Full physical output smoothness/compactness, with no output angular band. -/
theorem nativeFirstPhysicalCommutatorOut_smooth_compact
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (Cm : CRoom hreg δ0 W δ)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) (δr Ar : ℝ) (p : ℕ)
    (hδr : 0 < δr) (hAr : 0 < Ar) (q : ℝ) (h : MatrixField)
    (hh : ∀ i j, ContDiff ℝ ∞ (fun y => h y i j))
    (F0 : smoothCompactFiniteSphereCore hO hD)
    (hTF : ∀ x ∈ tsupport F0.val, (Tq δr Ar p q) x ∈ ParamRoom δ) :
    ContDiff ℝ ∞ (PO g2 δr Ar p q h F0) ∧ HasCompactSupport (PO g2 δr Ar p q h F0) := by
  have hc := nativeFirstPhysicalCommutator_smooth_compact g L y0 Φ B ε C ρ H a w hData
    hg hcalc hF hO hD τ0 hreg δ0 W δ Cm g2 hg2 δr Ar p hδr hAr q h hh F0 hTF
  have hs : ContDiff ℝ ∞ (PO g2 δr Ar p q h F0) :=
    (sphereSobolevHalfToSphereL2L hO hD).contDiff.comp hc.1
  have h0 : ∀ x ∉ tsupport (PC g2 δr Ar p q h F0), PO g2 δr Ar p q h F0 x = 0 := by
    intro x hx
    have hz := image_eq_zero_of_notMem_tsupport hx
    simp only [nativeFirstPhysicalCommutatorOut,hz,map_zero]
  exact ⟨hs,HasCompactSupport.intro hc.2 h0⟩

local notation "BETA" => actualReferenceBeta g L
local notation "TS" F0:max => tsupport (F0 : R3 → SphereL2)

/-- Original reference four-term physical form, with the actual composed commutator output. -/
def ActualScalarFirstPhysicalFormBound (δ : ℝ) (g2 : MatrixField) : Prop :=
  ∃ K : ℝ, 0 < K ∧ ∀ δr Ar : ℝ, ∀ p : ℕ,
    0 < δr → δr ≤ 1 → 0 < Ar → 1 ≤ p → ∀ q ∈ Icc (0 : ℝ) 1,
    ∀ eps : ℝ, 0 ≤ eps → eps ≤ 1 → ∀ h : MatrixField,
    (∀ i j, ContDiff ℝ ∞ (fun y => h y i j)) →
    ∀ F0 : smoothCompactFiniteSphereCore hO hD,
      (∀ x ∈ TS F0, (Tq δr Ar p q) x ∈ ParamRoom δ) →
      (∀ x ∈ TS F0, ∀ i j k l, PerturbedDensityAdjoint.TwoJetBound (coordinateDirection k) (coordinateDirection l)
        (fun y => h y i j) x (eps*referenceRadius δr Ar p L x)) →
      (∀ x ∈ TS F0, 1 ≤ BETA q δr Ar p x) →
      (∀ x ∈ TS F0, referenceRadius δr Ar p L x*(BETA q δr Ar p x)^2 ≤ eps) →
      Integrable (fun x => referenceDensityFamily g L (q,x)*⟪F0.val x, PO g2 δr Ar p q h F0 x⟫_ℝ) ∧
      Integrable (fun x => referenceDensityFamily g L (q,x)*
        finiteCoreReferenceProfileEnergy hO hD g hg L q (BETA q δr Ar p x) F0 x) ∧
      |∫ x, referenceDensityFamily g L (q,x)*⟪F0.val x, PO g2 δr Ar p q h F0 x⟫_ℝ| ≤
        K*eps*∫ x, referenceDensityFamily g L (q,x)*
          finiteCoreReferenceProfileEnergy hO hD g hg L q (BETA q δr Ar p x) F0 x
local notation "PhysicalForm" => ActualScalarFirstPhysicalFormBound
  g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0

/-- Actual scalar/S-first physical reference estimate with original hypotheses and before-profile K. -/
theorem exists_actual_scalar_first_physical_reference_form
    (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (δ : ℝ) (Cm : CRoom hreg δ0 W δ) (hL : 0 < L)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2) : PhysicalForm δ g2 := by
  obtain ⟨K,hK,hcap⟩ := exists_actual_scalar_first_commutator_reference_form
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg δ0 W δ Cm hL g2 hg2
  refine ⟨K,hK,?_⟩
  intro δr Ar p hδr hδr1 hAr hp q hq eps heps heps1 h hh F0 hTF hjet hbeta hsmall
  have hn := hcap δr Ar p hδr hδr1 hAr hp q hq eps heps heps1 h hh F0 hTF hjet hbeta hsmall
  have hglo := nativeFirstPhysicalCommutator_negative_graph g L y0 Φ B ε C ρ H a w hData
    hg hcalc hF hO hD τ0 hreg δ0 W δ Cm g2 hg2 δr Ar p hδr hAr q h hh F0 hTF
  have hp (x : R3) : sphereSobolevDualPairing (1/2 : ℝ) (halfInput hO hD F0 x)
      (NC g2 δr Ar p q h F0 x) = ⟪F0.val x,PO g2 δr Ar p q h F0 x⟫_ℝ :=
    ActualHigherSPhysicalPairing.physical_pairing_of_graph hO hD F0
      (PC g2 δr Ar p q h F0) (NC g2 δr Ar p q h F0) (fun y => congrFun hglo y) x
  have he : (fun x => referenceDensityFamily g L (q,x)*
      sphereSobolevDualPairing (1/2 : ℝ) (halfInput hO hD F0 x) (NC g2 δr Ar p q h F0 x)) =
      (fun x => referenceDensityFamily g L (q,x)*⟪F0.val x,PO g2 δr Ar p q h F0 x⟫_ℝ) := by
    funext x
    rw [hp x]
  have hpi : Integrable (fun x => referenceDensityFamily g L (q,x)*⟪F0.val x,PO g2 δr Ar p q h F0 x⟫_ℝ) :=
    he ▸ hn.1
  have hi := congrArg (fun J : R3 → ℝ => ∫ x, J x) he
  refine ⟨hpi,hn.2.1,?_⟩
  calc
    _ = |∫ x, referenceDensityFamily g L (q,x)*sphereSobolevDualPairing (1/2 : ℝ)
        (halfInput hO hD F0 x) (NC g2 δr Ar p q h F0 x)| := (congrArg abs hi).symm
    _ ≤ _ := hn.2.2

/-- Same chosen W and delta before the second metric, profiles and all finite inputs. -/
theorem exists_retained_actual_scalar_first_physical_reference_form
    (hreg : FixedDirichletRegularity) (hKernel : UnitBallValueTraceKernel τ0)
    (δ0 : ℝ) (hδ0 : 0 < δ0) (W : CoeffRoom δ0) (hL : 0 < L) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ δ0 ∧ δ ≤ ρ ∧ ∃ _Cm : CRoom hreg δ0 W δ,
      (∀ z ∈ commonRoom y0 ρ δ, ActualCommonQuadraticFormationConsumer.actualJacobianGuard g L Φ z) ∧
      ∀ g2 : MatrixField, IsAdmissibleMetric g2 → PhysicalForm δ g2 := by
  obtain ⟨δ,Cm,hJac⟩ := ActualCommonQuadraticFormationConsumer.exists_retained_common_formation_room
    g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 hreg hKernel δ0 hδ0 W
  refine ⟨δ,Cm.rev.pos,Cm.rev.le0,Cm.rev.leρ,Cm,hJac,?_⟩
  intro g2 hg2
  exact exists_actual_scalar_first_physical_reference_form g L y0 Φ B ε C ρ H a w hData
    hg hcalc hF hO hD τ0 hreg δ0 W δ Cm hL g2 hg2

end Native
end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualHigherSFirstPhysicalCommutatorGraph
