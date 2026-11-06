import Calderon.ActualUniformCompactKernelCutoff
import Calderon.ActualUniformFixedSeparationKernelJets
set_option autoImplicit false
set_option maxSynthPendingDepth 10
noncomputable section
open Set Metric Filter
open scoped ContDiff Topology
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask

theorem exists_uniform_smooth_fixed_separation_full_cross_kernel
    (S:KnownSideSourceData) (B d:ℝ) (hB:0 < B) (hd:0 < d):
    ∃ lambda0:ℝ,∃ C:ℕ→ℝ,0 < lambda0 ∧ (∀ n,0 < C n) ∧
      ∀ L lambda:ℝ,0 < lambda → lambda ≤ lambda0 →
      ∃ (Omega:Set (R3×R3)) (F G:R3×R3→ℝ),IsOpen Omega ∧
        Omega⊆dilatedOffDiagonal S lambda ∧ initialCross S lambda⊆Omega ∧
        fixedSeparationSet (B+1) (d/2)⊆Omega ∧ ProductSolutionOn S L lambda F Omega ∧
        (∀ z∈Omega,lambda • z.2∈S.W → F z=dilatedKernel1 S lambda z) ∧
        (∀ z∈Omega,lambda • z.1∈S.W → F z=dilatedKernel2 S lambda z) ∧
        ContDiff ℝ ∞ G ∧ HasCompactSupport G ∧
        (∀ z∈fixedSeparationSet B d,G=ᶠ[𝓝 z] F) ∧
        ∀ n:ℕ,∀ z:R3×R3,‖iteratedFDeriv ℝ n G z‖ ≤ C n := by
  obtain ⟨hU,hKU,hUF⟩ := fixedSeparationInteriorRoom_geometry B d hd
  obtain ⟨chi,hchi,hchic,hchiU,hchiOne⟩ := exists_compact_product_plateau_cutoff
    (fixedSeparationSet B d) (fixedSeparationInteriorRoom B d) (isCompact_fixedSeparationSet B d) hU hKU
  obtain ⟨A,hA,HA⟩ := exists_uniform_product_cutoff_joint_jet_bound
    (fixedSeparationInteriorRoom B d) hU chi hchi hchic hchiU
  obtain ⟨lambda0,J,hlambda0,hJ,HJ⟩ := fixed_separation_product_producer_with_uniform_joint_jets
    S (B+1) (d/2) (by positivity) (half_pos hd)
  have hJBound:∀ n:ℕ,∃ M:ℝ,0 < M ∧ ∀ j ≤ n,J j ≤ M := by
    intro n
    obtain ⟨m,hm⟩ := ((Finset.range (n+1)).finite_toSet.image J).bddAbove
    refine ⟨max m 1,zero_lt_one.trans_le (le_max_right _ _),?_⟩
    intro j hj
    exact (hm (Set.mem_image_of_mem J (by simpa only [Finset.mem_coe,Finset.mem_range] using Nat.lt_succ_of_le hj))).trans (le_max_left _ _)
  choose M hM HM using hJBound
  let C:ℕ→ℝ := fun n => A n*M n
  refine ⟨lambda0,C,hlambda0,(fun n => mul_pos (hA n) (hM n)),?_⟩
  intro L lambda hlam hlam0
  obtain ⟨Omega,F,hOmega,hRoom,hInitial,hCover,hF,hF1,hF2,hJets⟩ := HJ L lambda hlam hlam0
  have hUO:fixedSeparationInteriorRoom B d⊆Omega := hUF.trans hCover
  have hFU:ContDiffOn ℝ ∞ F (fixedSeparationInteriorRoom B d) := hF.1.mono hUO
  let G:R3×R3→ℝ := fun z => chi z*F z
  have hG:ContDiff ℝ ∞ G := contDiff_product_cutoff_mul _ hU chi hchi hchiU F hFU
  refine ⟨Omega,F,G,hOmega,hRoom,hInitial,hCover,hF,hF1,hF2,hG,hchic.mul_right,?_,?_⟩
  · intro z hz
    filter_upwards [hchiOne z hz] with w hw
    change chi w*F w=F w
    rw [hw,one_mul]
  · intro n z
    exact HA F hFU n (M n) (hM n).le (fun j hj w hw =>
      (hJets j w (hUF hw)).trans (HM n j hj)) z

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
