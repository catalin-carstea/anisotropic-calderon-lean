import Calderon.MixedKernelConstruction.MixedKernelNativeGlobalEnergyDelta
import Calderon.MixedKernelConstruction.MixedKernelCompactLevelGluing
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter ConnectionError ConformalDepth ActualScalarPrincipalAdjoint
open scoped ContDiff Topology

/-- One true parameter neighborhood controls the ORIGINAL radius uniformly over the SAME closed cylinder. -/
theorem exists_uniform_referenceRadius_delta_neighborhood
    (L delta Rstar : ℝ) (p : ℕ) (hd : 0<delta) (hRs : 0<Rstar)
    (w : ℝ) (hw : 0<w) :
    ∃ eta : ℝ, 0<eta ∧ eta<delta ∧ ∀ d ∈ Ioo (delta-eta) (delta+eta),
      0<d ∧ ∀ y ∈ cylinder,
        |referenceRadius d Rstar p L y-referenceRadius delta Rstar p L y|<w := by
  let D : Set (R3 × ℝ) := (univ : Set R3) ×ˢ Ioi (0 : ℝ)
  let f : R3 × ℝ → ℝ := fun a =>
    referenceRadius a.2 Rstar p L a.1-referenceRadius delta Rstar p L a.1
  have hD : IsOpen D := isOpen_univ.prod isOpen_Ioi
  have hR : ContinuousOn (fun a : R3 × ℝ => referenceRadius a.2 Rstar p L a.1) D :=
    (contDiffOn_referenceRadius_delta Rstar p L).continuousOn.comp
      (continuous_snd.prodMk continuous_fst).continuousOn
      (fun a ha => ⟨ha.2,mem_univ _⟩)
  have hBase : Continuous (fun a : R3 × ℝ => referenceRadius delta Rstar p L a.1) :=
    (contDiff_referenceRadius_actual delta Rstar p L hd hRs).continuous.comp continuous_fst
  have hf : ContinuousOn f D := hR.sub hBase.continuousOn
  let M : Set (R3 × ℝ) := D ∩ f ⁻¹' Ioo (-w) w
  have hM : IsOpen M := hf.isOpen_inter_preimage hD isOpen_Ioo
  have hLevel : cylinder ×ˢ {delta} ⊆ M := by
    rintro a ⟨ha,haD⟩
    have haEq : a.2=delta := haD
    refine ⟨⟨mem_univ _,?_⟩,?_⟩
    · simpa only [haEq,mem_Ioi] using hd
    · change -w<f a ∧ f a<w
      dsimp only [f]
      rw [haEq,sub_self]
      exact ⟨by linarith,hw⟩
  obtain ⟨V,hV,hCV,eps,heps,hSlab⟩ :=
    exists_compact_level_open_slab isCompact_cylinder delta hM hLevel
  let eta := min eps (delta/2)
  have hEta : 0<eta := lt_min heps (by linarith)
  have hEtaDelta : eta<delta := (min_le_right _ _).trans_lt (by linarith)
  refine ⟨eta,hEta,hEtaDelta,?_⟩
  intro d hdI
  have hdPos : 0<d := by linarith only [hEtaDelta,hdI.1]
  refine ⟨hdPos,?_⟩
  intro y hy
  have hDInt : d ∈ Ioo (delta-eps) (delta+eps) :=
    ⟨by linarith only [hdI.1,min_le_left eps (delta/2)],
      by linarith only [hdI.2,min_le_left eps (delta/2)]⟩
  have hPair : (y,d) ∈ M := hSlab (show (y,d) ∈ V ×ˢ Ioo (delta-eps) (delta+eps) from ⟨hCV hy,hDInt⟩)
  exact abs_lt.mpr hPair.2

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
