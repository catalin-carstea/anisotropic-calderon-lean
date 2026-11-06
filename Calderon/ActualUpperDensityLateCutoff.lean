import Calderon.ActualNativeSeedLateCutoff
import Calderon.ActualUniformKernelDensityJetBudget
import Calderon.ActualEligibleDensityRepresentationTransport
import Calderon.ActualUniformEligibleAnnularSeedJets
import Calderon.ActualRadiusBootstrapSmallJets
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap SphereHarmonic
open ConnectionError ConformalDepth ReferenceWeightedApproximation ActualScalarPrincipalAdjoint RadiusProfile

theorem exists_original_uniform_upper_eligible_density_first_jets_with_late_depth_cutoff
    (hcalc:FixedSobolevCalculus) (hreg:FixedDirichletRegularity)
    (hF:SphereFischerInner) (hO:OrthogonalSphereHarmonics) (hD:DenseSphereHarmonics)
    (tau0:UnitBallValueTrace) (S:KnownSideSourceData) (bound separation:ℝ)
    (hBound:0 < bound) (hSep:0 < separation):
    ∃ L0:ℝ,0 < L0 ∧ ∀ L:ℝ,L0 ≤ L →
      ∀ cover:NativeNormalCover S L,∃ p0:ℕ,2 ≤ p0 ∧ ∀ p:ℕ,p0 ≤ p →
      ∃ eps0:ℝ,0 < eps0 ∧ eps0 ≤ 1 ∧ ∀ eps:ℝ,0 < eps → eps ≤ eps0 →
      ∃ R0:ℝ,0 < R0 ∧ ∀ Rstar:ℝ,0 < Rstar → Rstar ≤ R0 → ∀ tb:ℝ,0 < tb →
      ∃ lambda0 D:ℝ,0 < lambda0 ∧ lambda0 ≤ cover.dilationCeiling ∧ 1 ≤ D ∧
      ∀ lambda:ℝ,0 < lambda → lambda ≤ lambda0 →
      ∀ delta:ℝ,0 < delta → delta ≤ 1 → CurrentRadiusBootstrap S L lambda delta Rstar eps p →
      (∀ delta'∈Icc delta (1:ℝ),∀ y∈cylinder,referenceRadius delta' Rstar p L y < cover.radiusCeiling) ∧
      Nonempty (ConstructedMixedKernel S L lambda delta Rstar bound separation p cover) ∧
      ∀ K:ConstructedMixedKernel S L lambda delta Rstar bound separation p cover,
      ∀ Psi:R3→SphereSobolev (3/2:ℝ),
      RepresentsNativeMixedKernelDensity hO hD tau0 S L lambda delta Rstar bound separation p cover K Psi →
      ∀ i:Fin cover.count,∀ U:Set R3,IsOpen U → U⊆interior cylinder∩(cover.packet i).centers →
      (∀ y∈U,tb ≤ referenceDepth L y) → ∀ y∈U,‖Psi y‖ ≤ D ∧ ‖fderiv ℝ Psi y‖ ≤ D := by
  obtain ⟨lu,hlu,HU⟩ := exists_uniform_native_density_representation_transport hO hD tau0 S
  obtain ⟨L0,hL0,H0⟩ := exists_original_uniform_native_seed_with_late_depth_cutoff S bound separation hBound hSep
  refine ⟨L0,hL0,?_⟩
  intro L hL
  have hLpos:0 < L := hL0.trans_le hL
  intro cover
  obtain ⟨R,hR,hRRoom,pN,hpN,HN⟩ := H0 L hL cover
  obtain ⟨pJ,hpJ,epsJ,hepsJ,hepsJ1,HJ⟩ := exists_uniform_referenceRadius_small_ordinary_jets_of_bootstrap
    S.g1 S.g1_admissible cylinder Geometry.isCompact_cylinder L hLpos (R/2) (half_pos hR)
  refine ⟨max pN pJ,hpN.trans (le_max_left _ _),?_⟩
  intro p hp
  have hpN':pN ≤ p := (le_max_left _ _).trans hp
  have hpJ':pJ ≤ p := (le_max_right _ _).trans hp
  obtain ⟨epsN,hepsN,hepsN1,HEN⟩ := HN p hpN'
  refine ⟨min epsN epsJ,lt_min hepsN hepsJ,(min_le_left _ _).trans hepsN1,?_⟩
  intro eps heps heps0
  have hepsN':eps ≤ epsN := heps0.trans (min_le_left _ _)
  have hepsJ':eps ≤ epsJ := heps0.trans (min_le_right _ _)
  obtain ⟨R0,hR0,HR⟩ := HEN eps heps hepsN'
  refine ⟨R0,hR0,?_⟩
  intro Rstar hRs hRs0 tb htb
  obtain ⟨tail,ln,J,hTail,hTailR,hTailQuarter,hTailTb,hln,hlnRoom,hJ,HNative⟩ := HR Rstar hRs hRs0 tb htb
  let a:ℝ := 2*tail
  let b:ℝ := 3*R/4
  have hta:tail < a := by dsimp only [a];linarith only [hTail]
  have ha:0 < a := by dsimp only [a];positivity
  have hb:b < R := by dsimp only [b];linarith only [hR]
  obtain ⟨D,hD0,HD⟩ := exists_nativeCover_high_density_budget_of_uniform_kernel_jets
    hcalc hreg hF hO hD tau0 S L cover a b J
  refine ⟨min ln lu,D,lt_min hln hlu,(min_le_left _ _).trans hlnRoom,hD0,?_⟩
  intro lambda hlam hlam0
  have hlamN:lambda ≤ ln := hlam0.trans (min_le_left _ _)
  have hlamU:lambda ≤ lu := hlam0.trans (min_le_right _ _)
  have hLam:lambda∈Icc (0:ℝ) cover.dilationCeiling := ⟨hlam.le,hlamN.trans hlnRoom⟩
  obtain ⟨H,G,hG,hGc,hHSol,hH1,hH2,hGerm,hJets,HK⟩ := HNative lambda hlam hlamN
  have hExtSeed:∀ q∈nativeMixedKernelAnnularSurface S L lambda a b cover,G=ᶠ[𝓝 q] H := by
    rintro q ⟨i,y,hy,r,hr,z,hz,rfl⟩
    exact hGerm i y hy r ⟨hta.le.trans hr.1,hr.2.trans hb.le⟩ z hz
  have hProfile:=HD G hG hJets lambda hLam
  intro delta hd hd1 hBoot
  obtain ⟨hRadius,Kcanon,hKSeed⟩ := HK delta hd hd1 hBoot
  have hRadiusCurrent:∀ y∈cylinder,referenceRadius delta Rstar p L y < cover.radiusCeiling :=
    fun y hy => hRadius delta ⟨le_rfl,hd1⟩ y hy
  have hJetRadius:∀ y∈cylinder,|referenceRadius delta Rstar p L y| ≤ R/2 ∧
      ‖fderiv ℝ (referenceRadius delta Rstar p L) y‖ ≤ 1 ∧
      ‖fderiv ℝ (fderiv ℝ (referenceRadius delta Rstar p L)) y‖ ≤ 1 := by
    intro y hy
    exact HJ p hpJ' lambda ⟨hlam.le,hLam.2.trans cover.dilation_le_one⟩ delta hd hd1 Rstar hRs eps heps.le hepsJ' y hy
      (hBoot.2 delta ⟨le_rfl,hd1⟩ y hy)
  refine ⟨hRadius,⟨Kcanon⟩,?_⟩
  intro K Psi hRep i U hU hURoom hDepth y hy
  have hRepCanon:=HU L cover lambda delta Rstar bound separation p K Kcanon Psi
    hlam hlamU hLam.2 hd hRs hRadiusCurrent hRep
  have hAnnulus:∀ z∈U,referenceRadius delta Rstar p L z∈Icc a b := by
    intro z hz
    have hzC:z∈cylinder := interior_subset (hURoom hz).1
    have hLower:Rstar*tb^p ≤ referenceRadius delta Rstar p L z := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ htb.le ((hDepth z hz).trans (le_softplus delta _ hd)) p) hRs.le
    have hUpper:referenceRadius delta Rstar p L z ≤ R/2 := (le_abs_self _).trans (hJetRadius z hzC).1
    constructor
    · dsimp only [a];linarith only [hLower,hTailTb,hTail]
    · dsimp only [b];linarith only [hUpper,hR]
  have h:=eligible_native_density_annular_firstJet_bound_of_uniform_profile_budget
    hcalc hreg hF hO hD tau0 S L lambda R tail a b cover hLam hR hRRoom hta ha hb H G hG hExtSeed D hProfile
    delta Rstar bound separation p Kcanon hKSeed Psi hRepCanon hd i U hU hURoom hAnnulus y hy
  exact ⟨h.1,h.2 (hJetRadius y (interior_subset (hURoom hy).1)).2.1⟩

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
