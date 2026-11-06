import Calderon.NativeHighSmoothMultiplierCompletedForcingTopology

/-! The strong inverse and its composition with its own completed forcing. -/
set_option autoImplicit false
noncomputable section
open Set Metric MeasureTheory
open scoped ENNReal ContDiff Gradient Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap
open EnergyBridge ConnectionError SphereHarmonic NativeCoefficientBoundaryMultiplier

variable (g : MatrixField) (L : ℝ) (y0 : R3)
  (Φ : ℝ → (R3 × R3) → ℝ → R3 × R3) (B : Set (R3 × R3)) (ε C ρ : ℝ)
  (H a : (ℝ × (R3 × ℝ)) × R3 → Matrix (Fin 3) (Fin 3) ℝ)
  (w : (ℝ × (R3 × ℝ)) × R3 → ℝ)
  (hData : JointConformalReferenceFramedDriftData g L y0 Φ B ε C ρ H a w)
  {T : Type} [NormedAddCommGroup T] [NormedSpace ℝ T] [FiniteDimensional ℝ T]
  (q : T × R3 → ℝ) (hq : ContDiff ℝ ∞ q) (Kq : Set R3) (hKq : IsCompact Kq)
  (hqz : ∀ t x, x ∉ Kq → q (t,x) = 0)

open NativeHarmonicLiftCompletion

lemma contDiffAt_joint_referenceStrongDriftFamily_inverse
    (hcalc : FixedSobolevCalculus) (s : ℕ) (p : ℝ × (R3 × ℝ))
    (hStrong : (referenceStrongDriftFamily
      g L y0 Φ B ε C ρ H a w hData hcalc s p.1 p.2).IsInvertible) :
    ContDiffAt ℝ ∞ (fun u : ℝ × (R3 × ℝ) =>
      (referenceStrongDriftFamily g L y0 Φ B ε C ρ H a w hData hcalc s u.1 u.2).inverse) p := by
  dbg_trace "INVERSE_COMPLETED_CUT INVERSE_BODY_ENTER"
  letI : CompleteSpace (StrongDirichletSpace s) := instCompleteSpaceStrongDirichletSpace s
  have hA := contDiff_joint_referenceStrongDriftFamily
    g L y0 Φ B ε C ρ H a w hData hcalc s
  dbg_trace "INVERSE_COMPLETED_CUT STRONG_FAMILY_READY"
  have hMap := hStrong.contDiffAt_map_inverse (n := ∞)
  dbg_trace "INVERSE_COMPLETED_CUT INVERSE_MAP_READY"
  exact hMap.comp p hA.contDiffAt

lemma contDiffAt_referenceHighSmoothMultiplierInverseCompletedForcing_commonSupport_joint
    (hcalc : FixedSobolevCalculus) (hF : SphereFischerInner)
    (p : ℝ × (R3 × ℝ)) (t : T)
    (hStrong : (referenceStrongDriftFamily
      g L y0 Φ B ε C ρ H a w hData hcalc 1 p.1 p.2).IsInvertible)
    (hLow : (referenceStrongDriftFamily
      g L y0 Φ B ε C ρ H a w hData hcalc 0 p.1 p.2).IsInvertible) :
    ContDiffAt ℝ ∞ (fun z : (ℝ × (R3 × ℝ)) × T =>
      (referenceStrongDriftFamily
        g L y0 Φ B ε C ρ H a w hData hcalc 1 z.1.1 z.1.2).inverse.comp
          ((referenceHighSmoothMultiplierCommutatorForcingFamily
            g L y0 Φ B ε C ρ H a w hData hcalc
            (commonSupportCoefficientFamily 3 q hq Kq hKq hqz z.2) z.1).comp
              ((referenceHarmonicLiftFamily
                g L y0 Φ B ε C ρ H a w hData hcalc 0 z.1.1 z.1.2).comp
                  (harmonicLiftCompletion hF)))) (p,t) := by
  dbg_trace "INVERSE_COMPLETED_CUT COMPOSITION_BODY_ENTER"
  have hInv := contDiffAt_joint_referenceStrongDriftFamily_inverse
    g L y0 Φ B ε C ρ H a w hData hcalc 1 p hStrong
  have hInvJoint := hInv.comp (p,t) contDiffAt_fst
  dbg_trace "INVERSE_COMPLETED_CUT INVERSE_PULLBACK_READY"
  have hCompleted := contDiffAt_referenceHighSmoothMultiplierCompletedForcing_commonSupport_joint
    g L y0 Φ B ε C ρ H a w hData q hq Kq hKq hqz hcalc hF p t hLow
  dbg_trace "INVERSE_COMPLETED_CUT COMPLETED_FORCING_READY"
  exact hInvJoint.clm_comp hCompleted

end OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap

#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_joint_referenceStrongDriftFamily_inverse
#print axioms OAI.AnisotropicCalderon.DirichletFamily.DriftBootstrap.contDiffAt_referenceHighSmoothMultiplierInverseCompletedForcing_commonSupport_joint
