import Calderon.ActualNativeKernelHighDensityUniformFirstJet
set_option autoImplicit false
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open EnergyBridge DirichletFamily DirichletFamily.DriftBootstrap ConnectionError ConformalDepth
open SphereHarmonic ReferenceWeightedApproximation ActualScalarPrincipalAdjoint

theorem exists_nativeCover_high_density_budget_of_uniform_kernel_jets
    (hcalc:FixedSobolevCalculus) (hreg:FixedDirichletRegularity)
    (hF:SphereFischerInner) (hO:OrthogonalSphereHarmonics) (hD:DenseSphereHarmonics)
    (tau0:UnitBallValueTrace) (S:KnownSideSourceData) (L:ℝ) (cover:NativeNormalCover S L)
    (a b:ℝ) (J:ℕ→ℝ):
    ∃ D:ℝ,1 ≤ D ∧ ∀ (G:R3×R3→ℝ) (hG:ContDiff ℝ ∞ G),
      (∀ n:ℕ,∀ z:R3×R3,‖iteratedFDeriv ℝ n G z‖ ≤ J n) →
      ∀ lambda∈Icc (0:ℝ) cover.dilationCeiling,∀ i:Fin cover.count,∀ y∈cylinder,∀ r∈Icc a b,
      ‖nativeMixedKernelHighDensity hcalc hF hO hD tau0 S L (cover.packet i) G hG (lambda,(y,r))‖ ≤ D ∧
      ‖fderiv ℝ (nativeMixedKernelHighDensity hcalc hF hO hD tau0 S L (cover.packet i) G hG) (lambda,(y,r))‖ ≤ D := by
  obtain ⟨A,hA,HA⟩ := exists_nativeCover_mixedKernelHighDensity_uniform_firstJet_bound
    hcalc hreg hF hO hD tau0 S L cover a b
  obtain ⟨J0,hJ0⟩ := ((Finset.range 6).finite_toSet.image J).bddAbove
  let M:ℝ := max J0 1
  have hM:0 < M := zero_lt_one.trans_le (le_max_right _ _)
  have hJM:∀ j ≤ 5,J j ≤ M := by
    intro j hj
    exact (hJ0 (Set.mem_image_of_mem J (by simpa only [Finset.mem_coe,Finset.mem_range] using (show j < 6 by omega)))).trans (le_max_left _ _)
  refine ⟨max (A*M) 1,le_max_right _ _,?_⟩
  intro G hG hJets lambda hlam i y hy r hr
  have h:=HA i G hG lambda hlam y hy r hr M hM.le (fun j hj z hz => (hJets j _).trans (hJM j hj))
  exact ⟨h.1.trans (le_max_left _ _),h.2.trans (le_max_left _ _)⟩

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
