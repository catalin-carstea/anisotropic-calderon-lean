import Calderon.MixedKernelConstruction.MixedKernelNativeRadialCoordinates
import Calderon.MixedKernelConstruction.MixedKernelCompatibleGluing
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter ConnectionError ConformalDepth
open scoped ContDiff Topology InnerProductSpace

/-- The actual canonical domain used to compare reached kernels. -/
def nativeRadialCanonicalRoom (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L)
    (lam R delta Rstar tail : ℝ) (p : ℕ) : Set (R3 × R3) :=
  nativeRadialSeedRoom S L C lam R tail ∪ nativeRadialOutsideRoom S L C lam R delta Rstar p

/-- Both pieces of the original canonical domain are genuinely open. -/
theorem isOpen_nativeRadialCanonicalRoom
    (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L)
    (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) C.dilationCeiling)
    (R : ℝ) (hR : 0<R) (hRoom : R<C.radiusCeiling)
    (delta Rstar tail : ℝ) (p : ℕ) (hd : 0<delta) (hRs : 0<Rstar) :
    IsOpen (nativeRadialCanonicalRoom S L C lam R delta Rstar tail p) :=
  (isOpen_nativeRadialSeedRoom S L C lam hlam R hR hRoom tail).union
    (isOpen_nativeRadialOutsideRoom S L C lam hlam R hR hRoom delta Rstar hd hRs p)

/-- Every actual canonical point has a nonzero ORIGINAL inverse velocity. -/
theorem nativeRadialCanonicalRoom_subset_radial_source
    (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L)
    (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) C.dilationCeiling)
    (R : ℝ) (hR : 0<R) (hRoom : R<C.radiusCeiling)
    (delta chartDelta Rstar tail : ℝ) (p : ℕ)
    (hd : 0<delta) (hcd : 0<chartDelta) (hRs : 0<Rstar) :
    nativeRadialCanonicalRoom S L C lam R delta Rstar tail p ⊆
      (nativeEnergyRadialChart S L C lam hlam R hR hRoom chartDelta Rstar p hcd hRs).source := by
  intro q hq
  rw [nativeEnergyRadialChart_source]
  rcases hq with hseed | ⟨a,ha,rfl⟩
  · exact ⟨hseed.1,hseed.2.1⟩
  · have hA : a ∈ nativeNormalVelocityRoom S L C R :=
      ⟨ha.1.1,by simpa only [mem_ball,dist_zero_right] using ha.2.2⟩
    refine ⟨⟨a,hA,rfl⟩,?_⟩
    change (nativeVelocityInverse S L C lam R (nativeVelocityPair S L C lam R a)).2≠0
    rw [nativeVelocityInverse_left S L C lam hlam R hR hRoom a hA]
    have hpos : 0<‖a.2‖ := (referenceRadius_pos delta Rstar p L a.1 hd hRs).trans ha.2.1
    exact norm_pos_iff.mp hpos

/-- A literal radial path in the actual target reaches the SAME delta-independent seed. -/
theorem nativeRadialCanonicalRoom_interval_seed
    (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L)
    (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) C.dilationCeiling)
    (R : ℝ) (hR : 0<R) (hRoom : R<C.radiusCeiling)
    (delta chartDelta Rstar tail : ℝ) (p : ℕ)
    (hd : 0<delta) (hcd : 0<chartDelta) (hRs : 0<Rstar) (htail : tail<R) :
    ∀ q ∈ nativeRadialCanonicalRoom S L C lam R delta Rstar tail p,
      ∃ (s h : ℝ) (f : ℝ → R3 × R3), ContinuousOn f (uIcc s h) ∧ f s=q ∧
        MapsTo f (uIcc s h) (nativeRadialCanonicalRoom S L C lam R delta Rstar tail p) ∧
        f h ∈ nativeRadialSeedRoom S L C lam R tail := by
  intro q hq
  let e := nativeEnergyRadialChart S L C lam hlam R hR hRoom chartDelta Rstar p hcd hRs
  have hqSource : q ∈ e.source :=
    nativeRadialCanonicalRoom_subset_radial_source S L C lam hlam R hR hRoom
      delta chartDelta Rstar tail p hd hcd hRs hq
  have hqTarget := e.map_source hqSource
  have hqT := hqTarget
  rw [nativeEnergyRadialChart_target] at hqT
  let r := referenceRadius chartDelta Rstar p L (e q).1.1
  let s := (e q).2
  let m := (tail+R)/2
  let h := max s (m-r)
  have hstart : s≤h := le_max_left _ _
  have hmR : m<R := by dsimp only [m];linarith
  have htm : tail < m := by dsimp only [m];linarith
  have hupper : h+r<R := by
    have h1 : s<R-r := by linarith only [hqT.2.2]
    have h2 : m-r<R-r := by linarith only [hmR]
    have hh : h<R-r := max_lt h1 h2
    linarith only [hh]
  have hlower : 0<s+r := hqT.2.1
  have hline : MapsTo (fun t : ℝ => ((e q).1,t)) (uIcc s h) e.target := by
    intro t ht
    rw [uIcc_of_le hstart] at ht
    rw [nativeEnergyRadialChart_target]
    exact ⟨hqT.1,by linarith only [hlower,ht.1],by linarith only [hupper,ht.2]⟩
  let f := fun t : ℝ => e.symm ((e q).1,t)
  have hf : ContinuousOn f (uIcc s h) := e.continuousOn_symm.comp
    (continuous_const.prodMk continuous_id).continuousOn hline
  have hinside : MapsTo f (uIcc s h)
      (nativeRadialCanonicalRoom S L C lam R delta Rstar tail p) := by
    intro t ht
    have hge : (e q).2≤t := by
      rw [uIcc_of_le hstart] at ht
      exact ht.1
    rcases hq with hseed | hold
    · exact Or.inl (nativeRadialSeedRoom_upward_in_nativeEnergyRadialChart S L C lam hlam R hR hRoom
        chartDelta Rstar tail p hcd hRs q ⟨hseed,hqSource⟩ t hge (hline ht))
    · exact Or.inr (nativeRadialOutsideRoom_upward_in_nativeEnergyRadialChart S L C lam hlam R hR hRoom
        chartDelta delta Rstar p hcd hd hRs q ⟨hold,hqSource⟩ t hge (hline ht))
  have hEndSource := e.map_target (hline right_mem_uIcc)
  rw [nativeEnergyRadialChart_source] at hEndSource
  have hEndData := nativeEnergyRadialChart_inverse_data S L C lam hlam R hR hRoom
    chartDelta Rstar p hcd hRs ((e q).1,h) (hline right_mem_uIcc)
  have hEndNorm : ‖(nativeVelocityInverse S L C lam R (f h)).2‖=h+r := hEndData.2
  have hmid : m≤h+r := by
    have hh : m-r≤h := le_max_right _ _
    linarith only [hh]
  refine ⟨s,h,f,hf,e.left_inv hqSource,hinside,hEndSource.1,hEndSource.2,Or.inr ?_⟩
  rw [hEndNorm]
  exact htm.trans_le hmid

/-- Actual radial reachability and the proved product UCP force complete canonical overlap equality. -/
theorem native_product_eq_on_radial_canonical_room
    (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L)
    (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) C.dilationCeiling)
    (R : ℝ) (hR : 0<R) (hRoom : R<C.radiusCeiling)
    (delta chartDelta Rstar tail : ℝ) (p : ℕ)
    (hd : 0<delta) (hcd : 0<chartDelta) (hRs : 0<Rstar) (htail : tail<R)
    {F G : R3 × R3 → ℝ}
    (hF : ProductSolutionOn S L lam F (nativeRadialCanonicalRoom S L C lam R delta Rstar tail p))
    (hG : ProductSolutionOn S L lam G (nativeRadialCanonicalRoom S L C lam R delta Rstar tail p))
    (heq : EqOn F G (nativeRadialSeedRoom S L C lam R tail)) :
    EqOn F G (nativeRadialCanonicalRoom S L C lam R delta Rstar tail p) := by
  apply native_product_eq_of_interval_seed S L lam
    (isOpen_nativeRadialCanonicalRoom S L C lam hlam R hR hRoom delta Rstar tail p hd hRs)
    (isOpen_nativeRadialSeedRoom S L C lam hlam R hR hRoom tail)
    subset_union_left hF hG heq
  exact nativeRadialCanonicalRoom_interval_seed S L C lam hlam R hR hRoom
    delta chartDelta Rstar tail p hd hcd hRs htail

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
