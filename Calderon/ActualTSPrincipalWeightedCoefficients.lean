import Calderon.ActualTSPrincipalCoefficients
import Calderon.ActualMixedAngularFullOutputForm
import Calderon.ActualHigherSScalarCommutatorNativeForm
import Calderon.ActualHigherSIntegratedPairing

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSPrincipalCoefficients
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualFullEGainedAssembly PrincipalCommutator ReferenceDensityBounds
  ActualScalarPrincipalAdjoint ActualHigherSScalarCommutatorForm ActualScalarPrincipalSelfFormBound
  ActualHigherSScalarCommutatorNativeForm ActualFiniteHarmonicCore ActualFiniteHarmonicModel
  ConformalDepth ReferenceWeightedApproximation
local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "Pphys" => ℝ × (R3 × ℝ)
local notation "Tpar" => Pphys × (R3 →L[ℝ] ℝ)
local notation "PP" => sphereSobolevDualPairing (1/2 : ℝ)
local notation "PL" => ActualHigherSScalarCommutatorNativeForm.halfDualPairingL
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete
@[instance_reducible] private def mixedNegDualNormed : NormedAddCommGroup (Neg →L[ℝ] ℝ) := inferInstance
@[instance_reducible] private def mixedNegDualSpace : NormedSpace ℝ (Neg →L[ℝ] ℝ) := inferInstance
@[instance_reducible] private def mixedLowNormed : NormedAddCommGroup (Half →L[ℝ] Neg) := inferInstance
@[instance_reducible] private def mixedLowSpace : NormedSpace ℝ (Half →L[ℝ] Neg) := inferInstance
attribute [local instance] mixedNegDualNormed mixedNegDualSpace mixedLowNormed mixedLowSpace

variable (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (hcalc : FixedSobolevCalculus) (τ0 : UnitBallValueTrace)
variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g)
local notation "CoeffRoom" => ActualFullEGainedEndpoints.CoefficientGermRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "Tq" dr:max Ar:max p:max q:max => ActualHigherSFormation.higherSParam L dr Ar p q

open ActualMixedAngularPairedGains ActualPiJacobiRadialGainedRows ActualJacobiAngularGainedRows NativeThreeHalfCoefficientMultiplier NativeCoefficientBoundaryMultiplier
  NativeOrderOneCoefficientMultiplier
local notation "IH" => sphereSobolevInclusionL (3/2 : ℝ) (1/2 : ℝ) (by norm_num)
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
local notation "EH" => canonicalHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "EL" => canonicalLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "eH" => orderedReverseHigh g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "eL" => orderedReverseLow g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "aH" => loweringHigh hF hO hD
local notation "aL" => loweringLow hF hO hD
local notation "AH" => raisingHigh hF hO hD
local notation "AL" => raisingLow hF hO hD
local notation "ParamRoom" δ:max => Set.prod (commonRoom y0 ρ δ) (closedBall (0 : R3 →L[ℝ] ℝ) 1)
local notation "Omega" => referenceRadialEndpointInvertibleLocus g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
local notation "CH" => loweringEHigh hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg
local notation "HH" => raisingReverseHigh hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg

attribute [local irreducible] canonicalHigh canonicalLow orderedReverseHigh orderedReverseLow
  nativeThreeHalfCoefficientMulL nativeHalfCoefficientMulL nativeNegativeHalfCoefficientMulL
  sphereSobolevInclusionL loweringHigh loweringLow raisingHigh raisingLow loweringEHigh raisingReverseHigh
  angularPrincipalHigh angularPrincipalTransposeHigh

section WeightedAlgebra
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma weighted_symmetric_sum (R : R3 → ℝ) (a b : Fin 3 → R3 → ℝ)
    (G Gt C Ct : Fin 3 → Fin 3 → R3 → E →L[ℝ] F) (x : R3)
    (h : ∀ i j, G i j x+Gt i j x=C i j x+Ct i j x) :
    weightedMixedSecondCoefficient R a b G x+weightedMixedSecondCoefficient R a b Gt x =
      weightedMixedSecondCoefficient R a b C x+weightedMixedSecondCoefficient R a b Ct x := by
  have he := congrArg (fun f : Fin 3 → Fin 3 → E →L[ℝ] F =>
    (R x)^2 • ∑ i : Fin 3, ∑ j : Fin 3, (a i x*b j x) • f i j)
    (funext (fun i => funext (fun j => h i j)))
  simpa only [weightedMixedSecondCoefficient,smul_add,Finset.sum_add_distrib] using he

lemma weighted_paired (P0 : E →L[ℝ] F →L[ℝ] ℝ)
    (R : R3 → ℝ) (a b : Fin 3 → R3 → ℝ)
    (G Gt : Fin 3 → Fin 3 → R3 → E →L[ℝ] F) (x : R3)
    (h : ∀ i j u v, P0 v (G i j x u)=P0 u (Gt i j x v)) (u v : E) :
    P0 v (weightedMixedSecondCoefficient R a b G x u)=
      P0 u (weightedMixedSecondCoefficient R a b Gt x v) := by
  simp only [weightedMixedSecondCoefficient,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sum_apply,map_smul,map_sum,smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [h i j u v]
end WeightedAlgebra

open ActualHigherSCoordinateWeightBounds ActualHigherSLeadingBracketGain SmoothMetricFrame MovingFrameConnection
local notation "PK" => angularPrincipalHigh hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg
local notation "PT" => angularPrincipalTransposeHigh hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg

def principalCoordinateCoefficient (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ)
    (l k : Fin 3) : R3 → Hi →L[ℝ] Neg :=
  weightedMixedSecondCoefficient (E := Hi) (F := Neg) (referenceRadius dr Ar p L)
    (fun i y => referenceMetricGramFrame g L (q,y) i l)
    (fun j y => firstCoordinateWeight g g2 L k j ((Tq dr Ar p q) y))
    (fun i j y => PK i j ((Tq dr Ar p q) y))

def principalTransposeCoordinateCoefficient (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ)
    (l k : Fin 3) : R3 → Hi →L[ℝ] Neg :=
  weightedMixedSecondCoefficient (E := Hi) (F := Neg) (referenceRadius dr Ar p L)
    (fun i y => referenceMetricGramFrame g L (q,y) i l)
    (fun j y => firstCoordinateWeight g g2 L k j ((Tq dr Ar p q) y))
    (fun i j y => PT i j ((Tq dr Ar p q) y))

def gainedCoordinateCoefficient (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (data : MixedAngularPhysicalEndpointRoom hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg hreg δ0 W)
    (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ) (l k : Fin 3) : R3 → Hi →L[ℝ] Neg :=
  weightedMixedSecondCoefficient (E := Hi) (F := Neg) (referenceRadius dr Ar p L)
    (fun i y => referenceMetricGramFrame g L (q,y) i l)
    (fun j y => firstCoordinateWeight g g2 L k j ((Tq dr Ar p q) y))
    (fun i j y => (JL).comp (CH hreg data.G δ0 W i j ((Tq dr Ar p q) y)))

def gainedTransposeCoordinateCoefficient (hreg : FixedDirichletRegularity) (δ0 : ℝ) (W : CoeffRoom δ0)
    (data : MixedAngularPhysicalEndpointRoom hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg hreg δ0 W)
    (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ) (l k : Fin 3) : R3 → Hi →L[ℝ] Neg :=
  weightedMixedSecondCoefficient (E := Hi) (F := Neg) (referenceRadius dr Ar p L)
    (fun i y => referenceMetricGramFrame g L (q,y) i l)
    (fun j y => firstCoordinateWeight g g2 L k j ((Tq dr Ar p q) y))
    (fun i j y => (JL).comp (-(HH hreg δ0 W i j ((Tq dr Ar p q) y))))

local notation "PC" => principalCoordinateCoefficient hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg
local notation "PCt" => principalTransposeCoordinateCoefficient hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg
local notation "GC" => gainedCoordinateCoefficient hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg
local notation "GCt" => gainedTransposeCoordinateCoefficient hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg

/-- All original scalar weights preserve the literal symmetric angular identity. -/
theorem principalCoordinate_symmetric_sum (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0)
    (data : MixedAngularPhysicalEndpointRoom hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg hreg δ0 W)
    (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ) (l k : Fin 3) (x : R3)
    (hx : (Tq dr Ar p q) x ∈ ParamRoom data.δ) :
    PC g2 dr Ar p q l k x+PCt g2 dr Ar p q l k x =
      GC hreg δ0 W data g2 dr Ar p q l k x+GCt hreg δ0 W data g2 dr Ar p q l k x := by
  apply ContinuousLinearMap.ext
  intro u
  simp only [principalCoordinateCoefficient,principalTransposeCoordinateCoefficient,
    gainedCoordinateCoefficient,gainedTransposeCoordinateCoefficient,weightedMixedSecondCoefficient,
    ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.comp_apply]
  conv_lhs => rw [←smul_add,←Finset.sum_add_distrib]
  conv_rhs => rw [←smul_add,←Finset.sum_add_distrib]
  apply congrArg (fun z : Neg => (referenceRadius dr Ar p L x)^2 • z)
  apply Finset.sum_congr rfl
  intro i _
  conv_lhs => rw [←Finset.sum_add_distrib]
  conv_rhs => rw [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro j _
  conv_lhs => rw [←smul_add]
  conv_rhs => rw [←smul_add]
  apply congrArg (fun z : Neg =>
    (referenceMetricGramFrame g L (q,x) i l*firstCoordinateWeight g g2 L k j ((Tq dr Ar p q) x)) • z)
  have h := congrArg (fun T : Hi →L[ℝ] Neg => T u)
    (angularPrincipalHigh_symmetric_sum hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg
      hreg δ0 W data i j ((Tq dr Ar p q) x) hx)
  simp only [ContinuousLinearMap.add_apply,ContinuousLinearMap.comp_apply] at h
  exact h

/-- The weighted product row has its actual paired transpose. -/
theorem principalCoordinate_paired (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0)
    (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ) (l k : Fin 3) (x : R3)
    (hx : (Tq dr Ar p q) x ∈ ParamRoom δ0)
    (hSeg : ∀ θ ∈ Icc (0 : ℝ) 1,
      (((Tq dr Ar p q) x).1.1,(((Tq dr Ar p q) x).1.2.1,θ*((Tq dr Ar p q) x).1.2.2)) ∈ Omega)
    (u v : Hi) :
    highDualPairingL v (PC g2 dr Ar p q l k x u)=highDualPairingL u (PCt g2 dr Ar p q l k x v) := by
  simp only [principalCoordinateCoefficient,principalTransposeCoordinateCoefficient,
    weightedMixedSecondCoefficient,ContinuousLinearMap.smul_apply,ContinuousLinearMap.sum_apply,
    map_smul,map_sum,smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  exact angularPrincipalHigh_paired hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg
    hreg δ0 W i j ((Tq dr Ar p q) x) hx hSeg u v

/-- C and the negative H retain their genuine transpose after the original scalar weights. -/
theorem gainedCoordinate_paired (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0)
    (data : MixedAngularPhysicalEndpointRoom hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg hreg δ0 W)
    (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ) (l k : Fin 3) (x : R3)
    (hx : (Tq dr Ar p q) x ∈ ParamRoom data.δ)
    (hSeg : ∀ θ ∈ Icc (0 : ℝ) 1,
      (((Tq dr Ar p q) x).1.1,(((Tq dr Ar p q) x).1.2.1,θ*((Tq dr Ar p q) x).1.2.2)) ∈ Omega)
    (u v : Hi) :
    highDualPairingL v (GC hreg δ0 W data g2 dr Ar p q l k x u)=
      highDualPairingL u (GCt hreg δ0 W data g2 dr Ar p q l k x v) := by
  simp only [gainedCoordinateCoefficient,gainedTransposeCoordinateCoefficient,
    weightedMixedSecondCoefficient,ContinuousLinearMap.smul_apply,ContinuousLinearMap.sum_apply,
    map_smul,map_sum,smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  exact angularGainHigh_paired hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg
    hreg δ0 W data i j ((Tq dr Ar p q) x) hx hSeg u v

/-- The gained coefficient is exactly the native-checked low coefficient after the original high inclusion. -/
theorem gainedCoordinate_eq_checked_coefficient (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0)
    (data : MixedAngularPhysicalEndpointRoom hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg hreg δ0 W)
    (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (q : ℝ) (l k : Fin 3) (x : R3)
    (hx : (Tq dr Ar p q) x ∈ ParamRoom data.δ) :
    GC hreg δ0 W data g2 dr Ar p q l k x =
      (mixedAngularSecondCoefficient hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg
        hreg δ0 W data g2 dr Ar p q l k x).comp IH := by
  apply ContinuousLinearMap.ext
  intro u
  have h := congrArg (fun T : Hi →L[ℝ] Neg => T u)
    (mixedAngularSecondCoefficient_upper_graph hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg
      hreg δ0 W data g2 dr Ar p q l k x hx)
  simpa only [gainedCoordinateCoefficient,mixedAngularSecondHighCoefficient,weightedMixedSecondCoefficient,
    ContinuousLinearMap.comp_apply,ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,map_sum,map_smul]
    using h.symm

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSPrincipalCoefficients
