import Calderon.ActualHighSmoothMultiplierBoundaryTopology

/-! Full upfront: day-oct13/actual-physical-density-operator-author-oct15-v001/
ACTUAL-HIGH-SMOOTH-MULTIPLIER-GAIN-EXPANSION-v001.md. Fixed actual multiplier, no chosen-jet smoothness premise. -/
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set
open scoped ContDiff
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)

attribute [local irreducible] referenceHighSmoothMultiplierBoundaryCommutatorFamily referenceStrongDriftFamily

lemma contDiffAt_referenceHighSmoothMultiplierBoundaryCommutatorFamily_fixed
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (hO : OrthogonalSphereHarmonics) (hD : DenseSphereHarmonics) (τ0 : UnitBallValueTrace)
    (Q : SmoothCoefficientJets 3) (p : ℝ × (R3 × ℝ))
    (hStrong : (referenceStrongDriftFamily
      g L y0 Φ B ε C ρ H a w hData hcalc 1 p.1 p.2).IsInvertible)
    (hLow : (referenceStrongDriftFamily
      g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2).IsInvertible) :
    ContDiffAt ℝ ∞ (referenceHighSmoothMultiplierBoundaryCommutatorFamily
      g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0 Q) p := by
  let m : ℝ × R3 → ℝ := fun z => coefficientValue 3 Q z.2
  have hm : ContDiff ℝ ∞ m := (contDiff_coefficientValue 3 Q).comp contDiff_snd
  let K : Set R3 := tsupport (coefficientValue 3 Q)
  have hK : IsCompact K := hasCompactSupport_coefficientValue 3 Q
  have hz : ∀ t x, x ∉ K → m (t,x)=0 := by
    intro t x hx
    change coefficientValue 3 Q x = 0
    exact image_eq_zero_of_notMem_tsupport hx
  have hQ (t : ℝ) : commonSupportCoefficientFamily 3 m hm K hK hz t = Q := by
    apply smoothCoefficientJets_eq_of_coefficientValue_eq 3
    funext x
    exact coefficientValue_commonSupportCoefficientFamily 3 m hm K hK hz t x
  have hJoint := contDiffAt_referenceHighSmoothMultiplierBoundaryCommutator_commonSupport_joint
    g L y0 Φ B ε C ρ H a w hData m hm K hK hz hcalc hF hO hD τ0 p 0 hStrong hLow
  have hComp := hJoint.comp p (contDiffAt_id.prodMk (contDiffAt_const (c := (0 : ℝ))))
  have hComp' : ContDiffAt ℝ ∞ (fun z : ℝ × (R3 × ℝ) =>
      referenceHighSmoothMultiplierBoundaryCommutatorFamily
        g L y0 Φ B ε C ρ H a w hData hcalc hF hO hD τ0
          (commonSupportCoefficientFamily 3 m hm K hK hz 0) z) p := by
    simpa only [Function.comp_def, id_eq] using hComp
  simpa only [hQ 0] using hComp'

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceHighSmoothMultiplierBoundaryCommutatorFamily_fixed

