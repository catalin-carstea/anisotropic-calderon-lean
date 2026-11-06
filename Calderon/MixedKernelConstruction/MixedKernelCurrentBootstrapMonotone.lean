import Calderon.MixedKernelConstruction.MixedKernelNativeGlobalEnergy
import Calderon.RadiusProfileBounds
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set ConnectionError ConformalDepth RadiusProfile

/-- The original smooth-max radius is monotone in its original positive delta parameter. -/
theorem referenceRadius_mono_delta
    (delta delta' Rstar : ℝ) (p : ℕ) (L : ℝ) (y : R3)
    (hd : 0<delta) (hle : delta ≤ delta') (hR : 0 ≤ Rstar) :
    referenceRadius delta Rstar p L y ≤ referenceRadius delta' Rstar p L y := by
  have hd' : 0<delta' := hd.trans_le hle
  have hSoft := (strictMonoOn_softplus_delta (referenceDepth L y)).monotoneOn hd hd' hle
  unfold referenceRadius
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (softplus_pos delta _ hd).le hSoft p) hR

/-- The current H8 bound and all-intermediate radius clause give the SAME original bootstrap at a later delta. -/
theorem currentRadiusBootstrap_mono_delta
    (S : KnownSideSourceData) (L lam delta delta' Rstar eps : ℝ) (p : ℕ)
    (hd : 0<delta) (hle : delta ≤ delta') (hR : 0 ≤ Rstar) (heps : 0 ≤ eps)
    (hBoot : CurrentRadiusBootstrap S L lam delta Rstar eps p) :
    CurrentRadiusBootstrap S L lam delta' Rstar eps p := by
  constructor
  · intro y hy
    exact (hBoot.1 y hy).trans (mul_le_mul_of_nonneg_left
      (referenceRadius_mono_delta delta delta' Rstar p L y hd hle hR) heps)
  · intro delta'' hd'' y hy
    exact hBoot.2 delta'' ⟨hle.trans hd''.1,hd''.2⟩ y hy

/-- The ONE global native energy has the exact reversed delta order, on every point of its original definition. -/
theorem nativeGlobalEnergy_antitone_delta
    (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L)
    (lam R delta delta' Rstar : ℝ) (p : ℕ) (q : R3 × R3)
    (hd : 0<delta) (hle : delta ≤ delta') (hR : 0<Rstar) :
    nativeGlobalEnergy S L C lam R delta' Rstar p q ≤ 
      nativeGlobalEnergy S L C lam R delta Rstar p q := by
  have hMono := referenceRadius_mono_delta delta delta' Rstar p L q.2 hd hle hR.le
  have hSq := pow_le_pow_left₀ (referenceRadius_pos delta Rstar p L q.2 hd hR).le hMono 2
  unfold nativeGlobalEnergy
  nlinarith only [hSq]

/-- Positive sides are nested in the SAME actual open normal image, with no interior-cylinder substitution. -/
theorem native_positive_energy_side_mono_delta
    (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L)
    (lam R delta delta' Rstar : ℝ) (p : ℕ)
    (hd : 0<delta) (hle : delta ≤ delta') (hR : 0<Rstar) :
    {q | q ∈ nativeNormalImage S L C lam R ∧ 0<nativeGlobalEnergy S L C lam R delta' Rstar p q}⊆
      {q | q ∈ nativeNormalImage S L C lam R ∧ 0<nativeGlobalEnergy S L C lam R delta Rstar p q} := by
  intro q hq
  exact ⟨hq.1,hq.2.trans_le (nativeGlobalEnergy_antitone_delta S L C lam R delta delta' Rstar p q hd hle hR)⟩

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
