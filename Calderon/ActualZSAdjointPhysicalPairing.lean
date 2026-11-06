import Calderon.ActualZHalfRealization
import Calderon.ActualSAdjointSecondNegative
import Calderon.ActualHigherSPhysicalPairing

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open Set Filter Metric MeasureTheory
open scoped BigOperators ContDiff Topology InnerProductSpace
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualZSAdjointPhysicalPairing
open EnergyBridge ConnectionError SphereHarmonic ActualAngularHighDraft ActualAngularPiDraft
  ActualFullEGainedEndpoints ActualHigherSFormation ActualSAdjointSecondNegative ActualZHalfRealization
  ReferenceDensityBounds ConformalDepth SmoothMetricFrame MovingFrameConnection
  ActualFiniteHarmonicCore ActualFiniteHarmonicModel ActualHigherSAdjointFormation ActualHigherSPhysicalPairing
  ActualCommonFirstWordQuadraticAdjoint

local notation "Hi" => SphereSobolev (3/2 : ℝ)
local notation "Half" => SphereSobolev (1/2 : ℝ)
local notation "Neg" => SphereSobolev (-(1/2 : ℝ))
local notation "JL" => sphereSobolevInclusionL (1/2 : ℝ) (-(1/2 : ℝ)) (by norm_num)
local notation "PP" => sphereSobolevDualPairing (1/2 : ℝ)
attribute [local instance] v017PiHighComplete v017PiHalfComplete v017PiNegativeComplete

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  (hg : IsAdmissibleMetric g) (hcalc : FixedSobolevCalculus)
  (hF : SphereFischerInner) (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics)
  (τ0 : UnitBallValueTrace)

local notation "CoeffRoom" => CoefficientGermRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "CRoom" => CommonFirstWordRoom g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
local notation "KL" => sphereSobolevHalfToSphereL2L hO hD

/-- Literal native Z/full Sdag physical equality on explicitly retained witnesses. -/
theorem native_Z_Sdag_pairing (hreg : FixedDirichletRegularity) (d0 : ℝ)
    (germs : CoeffRoom d0) (d : ℝ) (room : CRoom hreg d0 germs d)
    (g2 : MatrixField) (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD)
    (hT : ∀ z ∈ tsupport F.val, higherSParam L dr Ar p q z ∈
      Set.prod (commonRoom y0 ρ d) (closedBall (0 : R3 →L[ℝ] ℝ) 1))
    (x : R3) (hx : x ∈ tsupport F.val) :
    PP (referenceZHalf hF hO hD g L q dr Ar p x (higherSInput hO hD F x))
      (fullAdjointNegative g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q F x) =
      ⟪(nativeZ hO hD hF g hg L q dr Ar p hdr hAr F).val x,
        higherSAdjointOut g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
          hreg d0 germs g2 dr Ar p hdr hAr q F x⟫_ℝ := by
  let zh : Half := referenceZHalf hF hO hD g L q dr Ar p x (higherSInput hO hD F x)
  let ah : Half := higherSAdjointHalf g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg d0 germs g2 dr Ar p hdr hAr q F x
  have hGraph : JL ah =
      fullAdjointNegative g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0 g2 dr Ar p q F x :=
    fullAdjointNegative_inclusion g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
      hreg d0 germs d room g2 dr Ar p hdr hAr q F hT x hx
  have hZ : KL zh = (nativeZ hO hD hF g hg L q dr Ar p hdr hAr F).val x :=
    referenceZHalf_finiteCore_decode (hF := hF) (hO := hO) (hD := hD)
      g hg L q dr Ar p hdr hAr F x
  calc
    _ = PP zh (JL ah) := congrArg (fun z : Neg => PP zh z) hGraph.symm
    _ = ⟪KL zh,KL ah⟫_ℝ := halfPairing_eq_inner_sphereL2 hO hD zh ah
    _ = _ := congrArg (fun z : SphereL2 => ⟪z,KL ah⟫_ℝ) hZ

/-- Original smooth compact physical fields produce integrability on the same room. -/
theorem integrable_native_Z_Sdag (hreg : FixedDirichletRegularity) (d0 : ℝ)
    (germs : CoeffRoom d0) (d : ℝ) (room : CRoom hreg d0 germs d)
    (g2 : MatrixField) (hg2 : IsAdmissibleMetric g2)
    (dr Ar : ℝ) (p : ℕ) (hdr : 0 < dr) (hAr : 0 < Ar) (q : ℝ)
    (F : smoothCompactFiniteSphereCore hO hD)
    (hT : ∀ z ∈ tsupport F.val, higherSParam L dr Ar p q z ∈
      Set.prod (commonRoom y0 ρ d) (closedBall (0 : R3 →L[ℝ] ℝ) 1)) :
    Integrable (fun x => referenceDensityFamily g L (q,x)*
      ⟪(nativeZ hO hD hF g hg L q dr Ar p hdr hAr F).val x,
        higherSAdjointOut g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
          hreg d0 germs g2 dr Ar p hdr hAr q F x⟫_ℝ) := by
  let mu : R3 → ℝ := fun x => referenceDensityFamily g L (q,x)
  let z : R3 → SphereL2 := (nativeZ hO hD hF g hg L q dr Ar p hdr hAr F).val
  let v : R3 → SphereL2 := higherSAdjointOut g L y0 Φ B ε C ρ H a w hData hg hcalc hF hO hD τ0
    hreg d0 germs g2 dr Ar p hdr hAr q F
  let f : R3 → ℝ := fun x => mu x*⟪z x,v x⟫_ℝ
  have hmu : Continuous mu := (contDiff_referenceDensityFamily g hg L).continuous.comp
    (continuous_const.prodMk continuous_id)
  have hz : ContDiff ℝ ∞ z := (nativeZ hO hD hF g hg L q dr Ar p hdr hAr F).property.1
  have hv : ContDiff ℝ ∞ v := contDiff_higherSAdjointOut g L y0 Φ B ε C ρ H a w
    hData hg hcalc hF hO hD τ0 hreg d0 germs d room g2 hg2 dr Ar p hdr hAr q F hT
  have hf : Continuous f := hmu.mul (hz.continuous.inner hv.continuous)
  have hSupp : tsupport f ⊆ tsupport z := by
    apply closure_minimal ?_ (isClosed_tsupport z)
    intro x hx
    by_contra h
    have h0 : z x = 0 := image_eq_zero_of_notMem_tsupport h
    apply (Function.mem_support.1 hx)
    simp only [f,h0,inner_zero_left,mul_zero]
  have hCompact : HasCompactSupport f :=
    IsCompact.of_isClosed_subset (nativeZ hO hD hF g hg L q dr Ar p hdr hAr F).property.2.1
      (isClosed_tsupport f) hSupp
  exact hf.integrable_of_hasCompactSupport hCompact

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualZSAdjointPhysicalPairing

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualZSAdjointPhysicalPairing.native_Z_Sdag_pairing
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.ActualZSAdjointPhysicalPairing.integrable_native_Z_Sdag
