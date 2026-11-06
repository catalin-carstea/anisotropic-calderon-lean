import Calderon.ActualMixedKernelConstructionWithSeed
import Calderon.ActualReferenceBetaRadiusScale
import Calderon.ActualMixedKernelGlobalSurfaceExtension

set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open OAI.AnisotropicCalderon.ConformalDepth RadiusProfile ReferenceWeightedApproximation
  ActualHigherRadiusProfile

/-- The checked native mixed-kernel construction and genuine q=2 radius-beta
profile share the manuscript's ordered parameters. In particular Rstar is
chosen below one fixed ceiling and lambda below one fixed ceiling before all
delta; the kernel construction retains its seed across delta. -/
theorem exists_actual_kernel_beta_radius_profile_with_order
    (S : KnownSideSourceData) (bound separation : ℝ)
    (hBound : 0 < bound) (hSeparation : 0 < separation) :
    ∃ L0 : ℝ, 0 < L0 ∧ ∀ L : ℝ, L0 ≤ L →
    ∃ cover : NativeNormalCover S L,
    ∃ p0 : ℕ, 24 ≤ p0 ∧ ∀ p : ℕ, p0 ≤ p →
    ∃ eps0 : ℝ, 0 < eps0 ∧ eps0 ≤ 1 ∧
    ∀ eps : ℝ, 0 < eps → eps ≤ eps0 →
    ∃ R0 : ℝ, 0 < R0 ∧ ∀ Rstar : ℝ, 0 < Rstar → Rstar ≤ R0 →
    ∃ etaKernel : ℝ, 0 < etaKernel ∧ etaKernel ≤ cover.dilationCeiling ∧
      (∀ lam ∈ Icc (0 : ℝ) 1, ∀ delta : ℝ, 0 < delta → delta ≤ 1 →
        ∀ y ∈ cylinder,
          referenceRadius delta Rstar p L y *
            (actualReferenceBeta S.g1 L lam delta Rstar p y)^2 ≤ eps) ∧
      (∀ delta : ℝ, 0 < delta → delta ≤ 1 →
        ∀ y ∈ cylinder, referenceRadius delta Rstar p L y < cover.radiusCeiling) ∧
      (∀ lam : ℝ, 0 < lam → lam ≤ etaKernel →
        ∃ (R tail : ℝ) (Hseed : R3 × R3 → ℝ),
          0 < R ∧ R < cover.radiusCeiling ∧ 0 < tail ∧ tail < R ∧
          ProductSolutionOn S L lam Hseed (nativeRadialSeedRoom S L cover lam R tail) ∧
          ∀ delta : ℝ, 0 < delta → delta ≤ 1 →
            CurrentRadiusBootstrap S L lam delta Rstar eps p →
            (∀ delta' ∈ Icc delta (1 : ℝ), ∀ y ∈ cylinder,
              referenceRadius delta' Rstar p L y < cover.radiusCeiling) ∧
            ∃ KK : ConstructedMixedKernel S L lam delta Rstar bound separation p cover,
              nativeRadialSeedRoom S L cover lam R tail ⊆ KK.domain ∧
              EqOn KK.kernel Hseed (nativeRadialSeedRoom S L cover lam R tail)) := by
  obtain ⟨L0,hL0,hNativeL⟩ :=
    actual_mixed_kernel_exists_with_seed S bound separation hBound hSeparation
  refine ⟨L0,hL0,?_⟩
  intro L hL
  have hLpos : 0 < L := hL0.trans_le hL
  obtain ⟨cover,p0Native,hp0Native,hNativeP⟩ := hNativeL L hL
  obtain ⟨p0Beta,hqBeta,hp0Beta,hBetaP⟩ :=
    exists_fixed_actual_reference_beta_power_radius_profile
      S.g1 S.g1_admissible L hLpos cylinder isCompact_native_center_cylinder 2
  let p0 : ℕ := max 24 (max p0Native p0Beta)
  have hp0 : 24 ≤ p0 := le_max_left _ _
  refine ⟨cover,p0,hp0,?_⟩
  intro p hp
  have hpNative : p0Native ≤ p :=
    (le_max_left _ _).trans ((le_max_right _ _).trans hp)
  have hpBeta : p0Beta ≤ p :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hp)
  obtain ⟨eps0,heps0,heps01,hNativeEps⟩ := hNativeP p hpNative
  refine ⟨eps0,heps0,heps01,?_⟩
  intro eps heps hepsCap
  let eta : ℝ := min eps (min (cover.radiusCeiling/2) 1)
  have heta : 0 < eta := lt_min heps
    (lt_min (div_pos cover.radius_positive (by norm_num)) (by norm_num))
  have heta1 : eta ≤ 1 := (min_le_right _ _).trans (min_le_right _ _)
  have hetaEps : eta ≤ eps := min_le_left _ _
  have hetaCeil : eta < cover.radiusCeiling := by
    have h := (min_le_right eps (min (cover.radiusCeiling/2) 1)).trans
      (min_le_left _ _)
    linarith [cover.radius_positive]
  obtain ⟨RB,hRB,hBetaProfile⟩ := hBetaP p hpBeta eta heta heta1
  obtain ⟨RN,hRN,hNativeR⟩ := hNativeEps eps heps hepsCap
  let R0 : ℝ := min RB RN
  have hR0 : 0 < R0 := lt_min hRB hRN
  refine ⟨R0,hR0,?_⟩
  intro Rstar hRstar hRstarCap
  have hRstarB : Rstar ≤ RB := hRstarCap.trans (min_le_left _ _)
  have hRstarN : Rstar ≤ RN := hRstarCap.trans (min_le_right _ _)
  obtain ⟨etaKernel,hEtaKernel,hEtaKernelCover,hNativeLam⟩ :=
    hNativeR Rstar hRstar hRstarN
  have hBudget : ∀ lam ∈ Icc (0 : ℝ) 1, ∀ delta : ℝ, 0 < delta → delta ≤ 1 →
      ∀ y ∈ cylinder,
        referenceRadius delta Rstar p L y *
          (actualReferenceBeta S.g1 L lam delta Rstar p y)^2 ≤ eps := by
    intro lam hlam delta hdelta hdeltaOne y hy
    have hAtRB := (hBetaProfile lam hlam delta hdelta hdeltaOne y hy).2.1
    have hMono := referenceRadius_beta_sq_mono_scale
      S.g1 L lam delta Rstar RB p y hdelta hRstar hRB hRstarB
    exact hMono.1.trans (hAtRB.trans hetaEps)
  have hRoom : ∀ delta : ℝ, 0 < delta → delta ≤ 1 →
      ∀ y ∈ cylinder, referenceRadius delta Rstar p L y < cover.radiusCeiling := by
    intro delta hdelta hdeltaOne y hy
    have hAtRB := (hBetaProfile 0 (by constructor <;> norm_num)
      delta hdelta hdeltaOne y hy).2.2
    have hMono := referenceRadius_beta_sq_mono_scale
      S.g1 L 0 delta Rstar RB p y hdelta hRstar hRB hRstarB
    exact (hMono.2.trans hAtRB).trans_lt hetaCeil
  refine ⟨etaKernel,hEtaKernel,hEtaKernelCover,hBudget,hRoom,?_⟩
  intro lam hlam hLamCap
  exact hNativeLam lam hlam hLamCap

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
