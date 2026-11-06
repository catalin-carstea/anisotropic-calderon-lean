import Calderon.ActualTSPrincipalGreen
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

/-- Continuous native high/negative pairing, using only the original inclusion. -/
def highDualPairingL : Hi →L[ℝ] Neg →L[ℝ] ℝ := (PL).comp IH
lemma highDualPairingL_apply (u : Hi) (z : Neg) : highDualPairingL u z=PP (IH u) z := rfl

/-- Literal principal angular product difference aE-Ae. -/
def angularPrincipalHigh (i j : Fin 3) (t : Tpar) : Hi →L[ℝ] Neg :=
  (aL i).comp (EH j t)-(AL i).comp (eH j t)

/-- Genuine paired transpose eA-Ea, with the same i,j. -/
def angularPrincipalTransposeHigh (i j : Fin 3) (t : Tpar) : Hi →L[ℝ] Neg :=
  (eL j t).comp (AH i)-(EL j t).comp (aH i)

attribute [local irreducible] canonicalHigh canonicalLow orderedReverseHigh orderedReverseLow
  nativeThreeHalfCoefficientMulL nativeHalfCoefficientMulL nativeNegativeHalfCoefficientMulL
  sphereSobolevInclusionL loweringHigh loweringLow raisingHigh raisingLow loweringEHigh raisingReverseHigh

/-- The actual signed principal products have the claimed native transpose. -/
theorem angularPrincipalHigh_paired (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0) (i j : Fin 3) (t : Tpar) (ht : t ∈ ParamRoom δ0)
    (hSeg : ∀ θ ∈ Icc (0 : ℝ) 1, (t.1.1,(t.1.2.1,θ*t.1.2.2)) ∈ Omega)
    (u v : Hi) :
    highDualPairingL v (angularPrincipalHigh hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg i j t u)=
      highDualPairingL u (angularPrincipalTransposeHigh hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg i j t v) := by
  have hForwardCompat (z : Hi) : JL (EH j t z)=EL j t (IH z) := by
    have hp := (W.piGerm j t ht).self_of_nhds
    exact canonicalHigh_low_compatibility g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg j t hSeg (piJets g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 δ0 W j t)
      hp.1 hp.2.1 z
  have hReverseCompat (z : Hi) : JL (eH j t z)=eL j t (IH z) := by
    have hp := (W.piGerm j t ht).self_of_nhds
    simpa only [orderedReverseHigh,orderedReverseLow,originalRadialReverseHigh,
      originalRadialReverseLow,jacobiAngularReverseHigh,jacobiAngularReverseLow] using
      explicit_ordered_reverse_high_low_compatibility g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        j t hSeg (piJets g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 δ0 W j t)
        hp.2.1 hp.2.2 z
  have hPivot (x y : Half) : PP x (EL j t y)=PP y (eL j t x) := by
    have hp := (W.piGerm j t ht).self_of_nhds
    simpa only [orderedReverseLow,originalRadialReverseLow,jacobiAngularReverseLow] using
      canonicalLow_explicit_ordered_reverse_pairing g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
        j t hSeg (piJets g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 δ0 W j t)
        hp.2.1 hp.2.2 x y
  have hForward (z : Hi) (x : Half) : PP (IH z) (EL j t x)=PP x (JL (eH j t z)) :=
    (hPivot (IH z) x).trans (congrArg (PP x) (hReverseCompat z).symm)
  have hReverse (z : Hi) (x : Half) : PP (IH z) (eL j t x)=PP x (JL (EH j t z)) :=
    (hPivot x (IH z)).symm.trans (congrArg (PP x) (hForwardCompat z).symm)
  have h1 : PP (IH v) (aL i (EH j t u))=PP (IH u) (eL j t (AH i v)) :=
    (v017_aA1 hF hO hD i v (EH j t u)).trans
      ((v016_pairing_inclusion_symm (EH j t u) (AH i v)).trans
        (hReverse u (AH i v)).symm)
  have h2 : PP (IH v) (AL i (eH j t u))=PP (IH u) (EL j t (aH i v)) :=
    (v017_aA2 hF hO hD i v (eH j t u)).symm.trans (hForward u (aH i v)).symm
  simpa only [highDualPairingL_apply,angularPrincipalHigh,angularPrincipalTransposeHigh,
    ContinuousLinearMap.sub_apply,ContinuousLinearMap.comp_apply,v016_pairing_sub_right] using
    congrArg₂ (fun x y : ℝ => x-y) h1 h2

private lemma four_term_symmetric_sum {V : Type*} [AddCommGroup V] (a b c d : V) :
    (a-b)+(c-d)=(a-d)+(-(b-c)) := by
  abel

/-- The symmetric product sum is exactly C-H, preserving both original mixed graphs. -/
theorem angularPrincipalHigh_symmetric_sum (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0)
    (data : MixedAngularPhysicalEndpointRoom hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg hreg δ0 W)
    (i j : Fin 3) (t : Tpar) (ht : t ∈ ParamRoom data.δ) :
    angularPrincipalHigh hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg i j t+
      angularPrincipalTransposeHigh hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg i j t =
      (JL).comp (CH hreg data.G δ0 W i j t)+(JL).comp (-(HH hreg δ0 W i j t)) := by
  apply ContinuousLinearMap.ext
  intro u
  have hc := (data.graphs i j t ht).1 u
  have hh := (data.graphs i j t ht).2.1 u
  simp only [angularPrincipalHigh,angularPrincipalTransposeHigh,ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply,ContinuousLinearMap.comp_apply,ContinuousLinearMap.neg_apply,map_neg,hc,hh]
  exact four_term_symmetric_sum _ _ _ _

/-- Genuine C and -H pairing, on the same caller W and the same ordered indices. -/
theorem angularGainHigh_paired (hreg : FixedDirichletRegularity)
    (δ0 : ℝ) (W : CoeffRoom δ0)
    (data : MixedAngularPhysicalEndpointRoom hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg hreg δ0 W)
    (i j : Fin 3) (t : Tpar) (ht : t ∈ ParamRoom data.δ)
    (hSeg : ∀ θ ∈ Icc (0 : ℝ) 1, (t.1.1,(t.1.2.1,θ*t.1.2.2)) ∈ Omega)
    (u v : Hi) :
    highDualPairingL v (JL (CH hreg data.G δ0 W i j t u))=
      highDualPairingL u (JL ((-(HH hreg δ0 W i j t)) v)) := by
  rw [highDualPairingL_apply,highDualPairingL_apply]
  have ht0 : t ∈ ParamRoom δ0 := ⟨commonRoom_mono y0 ρ data.δ_le0 ht.1,ht.2⟩
  exact mixed_high_pairing_of_graphs hF hO hD hcalc τ0 g L y0 Φ B ε C ρ H a w hData hg
    hreg δ0 W i j t ht0 hSeg (CH hreg data.G δ0 W i j t) (HH hreg δ0 W i j t)
    (data.graphs i j t ht).1 (data.graphs i j t ht).2.1 u v



end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualTSPrincipalCoefficients
