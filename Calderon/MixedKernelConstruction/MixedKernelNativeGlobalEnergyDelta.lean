import Calderon.MixedKernelConstruction.MixedKernelNativeGlobalEnergy
import Calderon.RadiusProfileBounds
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter ConformalDepth RadiusProfile
open scoped ContDiff Topology InnerProductSpace

/-- The literal original radius is jointly smooth in positive delta and the physical center. -/
theorem contDiffOn_referenceRadius_delta (Rstar : ℝ) (p : ℕ) (L : ℝ) :
    ContDiffOn ℝ ∞ (fun a : ℝ × R3 => referenceRadius a.1 Rstar p L a.2)
      (Ioi (0 : ℝ) ×ˢ (univ : Set R3)) := by
  let A := Ioi (0 : ℝ) ×ˢ (univ : Set R3)
  have hDelta : ContDiffOn ℝ ∞ (fun a : ℝ × R3 => a.1) A := contDiff_fst.contDiffOn
  have hDepth : ContDiffOn ℝ ∞ (fun a : ℝ × R3 => referenceDepth L a.2) A :=
    ((contDiff_referenceDepth L).comp contDiff_snd).contDiffOn
  have hQuot : ContDiffOn ℝ ∞ (fun a : ℝ × R3 => referenceDepth L a.2/a.1) A :=
    hDepth.div hDelta (fun a ha => ha.1.ne')
  have hLog : ContDiffOn ℝ ∞ (fun a : ℝ × R3 => Real.log (1+Real.exp (referenceDepth L a.2/a.1))) A :=
    (contDiff_const.contDiffOn.add hQuot.exp).log (fun a _ => by positivity)
  change ContDiffOn ℝ ∞ (fun a : ℝ × R3 => Rstar*(a.1*Real.log (1+Real.exp (referenceDepth L a.2/a.1)))^p) A
  exact contDiff_const.contDiffOn.mul ((hDelta.mul hLog).pow p)

/-- The ONE actual global phase is jointly smooth in its positive shrinking parameter and physical variables. -/
theorem contDiffOn_nativeGlobalEnergy_delta
    (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L)
    (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) C.dilationCeiling)
    (R : ℝ) (hR : 0<R) (hRoom : R<C.radiusCeiling) (Rstar : ℝ) (p : ℕ) :
    ContDiffOn ℝ ∞ (fun a : ℝ × (R3 × R3) => nativeGlobalEnergy S L C lam R a.1 Rstar p a.2)
      (Ioi (0 : ℝ) ×ˢ nativeNormalImage S L C lam R) := by
  let U := nativeNormalImage S L C lam R
  let V := Ioi (0 : ℝ) ×ˢ U
  have hInv := contDiffOn_nativeVelocityInverse S L C lam hlam R hR hRoom
  have hVelocity : ContDiffOn ℝ ∞ (fun a : ℝ × (R3 × R3) =>
      (nativeVelocityInverse S L C lam R a.2).2) V :=
    (hInv.comp contDiff_snd.contDiffOn (fun a ha => ha.2)).snd
  have hProj : ContDiffOn ℝ ∞ (fun a : ℝ × (R3 × R3) => (a.1,a.2.2)) V :=
    (contDiff_fst.prodMk contDiff_snd.snd).contDiffOn
  have hRadius : ContDiffOn ℝ ∞ (fun a : ℝ × (R3 × R3) => referenceRadius a.1 Rstar p L a.2.2) V :=
    (contDiffOn_referenceRadius_delta Rstar p L).comp hProj (fun a ha => ⟨ha.1,mem_univ _⟩)
  change ContDiffOn ℝ ∞ (fun a : ℝ × (R3 × R3) =>
    (⟪(nativeVelocityInverse S L C lam R a.2).2,(nativeVelocityInverse S L C lam R a.2).2⟫_ℝ-
      (referenceRadius a.1 Rstar p L a.2.2)^2)/2) V
  exact ((ContDiffOn.inner ℝ hVelocity hVelocity).sub (hRadius.pow 2)).div_const 2

/-- Joint continuity retains the SAME phase and the SAME actual open normal image. -/
theorem continuousOn_nativeGlobalEnergy_delta
    (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L)
    (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) C.dilationCeiling)
    (R : ℝ) (hR : 0<R) (hRoom : R<C.radiusCeiling) (Rstar : ℝ) (p : ℕ) :
    ContinuousOn (fun a : ℝ × (R3 × R3) => nativeGlobalEnergy S L C lam R a.1 Rstar p a.2)
      (Ioi (0 : ℝ) ×ˢ nativeNormalImage S L C lam R) :=
  (contDiffOn_nativeGlobalEnergy_delta S L C lam hlam R hR hRoom Rstar p).continuousOn

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
