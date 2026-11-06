import Calderon.MixedKernelConstruction.MixedKernelNativeRadialSeedBoundary
import Calderon.MixedKernelConstruction.MixedKernelCurrentBootstrapMonotone
import Calderon.MixedKernelConstruction.MixedKernelCompactLevelGluing
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter ConnectionError ConformalDepth
open scoped ContDiff Topology InnerProductSpace

/-- The SAME closed cylinder and WHOLE actual unit-direction base are compact. -/
theorem isCompact_native_radial_base :
    IsCompact (cylinder ×ˢ (univ : Set (sphere (0 : R3) 1))) :=
  isCompact_cylinder.prod isCompact_univ

/-- Actual zero-height target points are literally original native-front points, including all boundary centers. -/
theorem nativeEnergyRadialChart_zero_level_mem_front
    (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L)
    (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) C.dilationCeiling)
    (R : ℝ) (hR : 0<R) (hRoom : R<C.radiusCeiling)
    (c Rstar : ℝ) (p : ℕ) (hc : 0<c) (hRs : 0<Rstar)
    (hRadius : ∀ y ∈ cylinder, referenceRadius c Rstar p L y<R)
    (b : R3 × sphere (0 : R3) 1) (hb : b.1 ∈ cylinder) :
    let e := nativeEnergyRadialChart S L C lam hlam R hR hRoom c Rstar p hc hRs
    (b,0) ∈ e.target ∧ e.symm (b,0) ∈ nativeSphereFront S L C lam c Rstar p := by
  intro e
  obtain ⟨i,hi⟩ := C.covers_cylinder b.1 hb
  have hCenter : b.1 ∈ nativeCoverCenterRoom S L C := mem_iUnion.mpr ⟨i,hi⟩
  let r := referenceRadius c Rstar p L b.1
  have hr : 0<r := referenceRadius_pos c Rstar p L b.1 hc hRs
  have hrR : r<R := hRadius b.1 hb
  have hOmega : ‖(b.2 : R3)‖=1 := by simpa only [mem_sphere,dist_zero_right] using b.2.property
  have hTarget : (b,0) ∈ e.target := by
    rw [nativeEnergyRadialChart_target]
    exact ⟨hCenter,by simpa only [zero_add] using hr,by simpa only [zero_add] using hrR⟩
  refine ⟨hTarget,?_⟩
  have hInv := nativeEnergyRadialChart_inverse S L C lam hlam R hR hRoom c Rstar p hc hRs
    (b,0) (by simpa only [zero_add] using hr)
  simp only [zero_add] at hInv
  rw [hInv]
  refine ⟨(b.1,(b.2 : R3)),⟨hb,b.2.property⟩,?_⟩
  have hBall : (b.2 : R3) ∈ closedBall (0 : R3) 2 := by
    simp only [mem_closedBall,dist_zero_right,hOmega]
    norm_num
  change (nativeCoverEndpoint S L C lam ((b.1,r),(b.2 : R3)),b.1)=
    nativeVelocityPair S L C lam R (b.1,r • (b.2 : R3))
  rw [nativeCoverEndpoint_eq_packet S L C lam hlam i b.1 hi r hr (hrR.trans hRoom) (b.2 : R3) hBall]
  exact packetEndpoint_pair_eq_nativeVelocityPair S L C lam hlam R hR hRoom i b.1 hi r hr hrR (b.2 : R3) hOmega

/-- A genuine open neighborhood of the ENTIRE native front contains one uniform ACTUAL chart slab. -/
theorem exists_native_whole_front_actual_slab
    (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L)
    (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) C.dilationCeiling)
    (R : ℝ) (hR : 0<R) (hRoom : R<C.radiusCeiling)
    (c Rstar : ℝ) (p : ℕ) (hc : 0<c) (hRs : 0<Rstar)
    (hRadius : ∀ y ∈ cylinder, referenceRadius c Rstar p L y<R)
    (U : Set (R3 × R3)) (hU : IsOpen U) (hFront : nativeSphereFront S L C lam c Rstar p ⊆ U) :
    let e := nativeEnergyRadialChart S L C lam hlam R hR hRoom c Rstar p hc hRs
    ∃ V : Set (R3 × sphere (0 : R3) 1), IsOpen V ∧ cylinder ×ˢ univ ⊆ V ∧
      ∃ w : ℝ, 0<w ∧ V ×ˢ Ioo (-w) w ⊆ e.target ∧ MapsTo e.symm (V ×ˢ Ioo (-w) w) U := by
  intro e
  have hTarget : (cylinder ×ˢ (univ : Set (sphere (0 : R3) 1))) ×ˢ {(0 : ℝ)} ⊆ e.target := by
    rintro ⟨b,t⟩ ⟨hb,ht⟩
    have ht0 : t=0 := ht
    subst t
    exact (nativeEnergyRadialChart_zero_level_mem_front S L C lam hlam R hR hRoom c Rstar p hc hRs hRadius b hb.1).1
  have hLevel : ∀ a ∈ (cylinder ×ˢ (univ : Set (sphere (0 : R3) 1))) ×ˢ {(0 : ℝ)}, e.symm a ∈ U := by
    rintro ⟨b,t⟩ ⟨hb,ht⟩
    have ht0 : t=0 := ht
    subst t
    exact hFront (nativeEnergyRadialChart_zero_level_mem_front S L C lam hlam R hR hRoom c Rstar p hc hRs hRadius b hb.1).2
  simpa only [zero_sub,zero_add] using
    exists_actual_chart_compact_level_slab e isCompact_native_radial_base 0 hU hTarget hLevel

/-- BOTH the new strict outside shell and the WHOLE new zero front have genuine old-chart height in (-w,0]. -/
theorem native_new_level_mem_old_outside_or_actual_slab
    (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L)
    (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) C.dilationCeiling)
    (R : ℝ) (hR : 0<R) (hRoom : R<C.radiusCeiling)
    (b c Rstar : ℝ) (p : ℕ) (hb : 0<b) (hc : 0<c) (hbc : b≤c) (hRs : 0<Rstar)
    (hRadiusB : ∀ y ∈ cylinder, referenceRadius b Rstar p L y<R)
    (w : ℝ) (hClose : ∀ y ∈ cylinder, |referenceRadius b Rstar p L y-referenceRadius c Rstar p L y|<w) :
    let e := nativeEnergyRadialChart S L C lam hlam R hR hRoom c Rstar p hc hRs
    ∀ q ∈ nativeRadialOutsideRoom S L C lam R b Rstar p ∪ nativeSphereFront S L C lam b Rstar p,
      q ∈ nativeRadialOutsideRoom S L C lam R c Rstar p ∨
        (q ∈ e.source ∧ (e q).1 ∈ cylinder ×ˢ (univ : Set (sphere (0 : R3) 1)) ∧
          -w<(e q).2 ∧ (e q).2≤0) := by
  intro e q hq
  by_cases hOld : q ∈ nativeRadialOutsideRoom S L C lam R c Rstar p
  · exact Or.inl hOld
  have conclude (hN : q ∈ nativeNormalImage S L C lam R) (hCyl : q.2 ∈ cylinder)
      (hLow : referenceRadius b Rstar p L q.2≤‖(nativeVelocityInverse S L C lam R q).2‖)
      (hUp : ‖(nativeVelocityInverse S L C lam R q).2‖≤referenceRadius c Rstar p L q.2) :
      q ∈ e.source ∧ (e q).1 ∈ cylinder ×ˢ (univ : Set (sphere (0 : R3) 1)) ∧ -w<(e q).2 ∧ (e q).2≤0 := by
    have hv : (nativeVelocityInverse S L C lam R q).2≠0 :=
      norm_pos_iff.mp ((referenceRadius_pos b Rstar p L q.2 hb hRs).trans_le hLow)
    have hSource : q ∈ e.source := by
      rw [nativeEnergyRadialChart_source]
      exact ⟨hN,hv⟩
    have hBase : (e q).1 ∈ cylinder ×ˢ (univ : Set (sphere (0 : R3) 1)) := by
      refine ⟨?_,mem_univ _⟩
      rw [nativeEnergyRadialChart_center S L C lam hlam R hR hRoom c Rstar p hc hRs q hN]
      exact hCyl
    have hHeight : (e q).2=‖(nativeVelocityInverse S L C lam R q).2‖-referenceRadius c Rstar p L q.2 :=
      nativeEnergyRadialChart_height S L C lam hlam R hR hRoom c Rstar p hc hRs q hN hv
    have hDiff := (abs_lt.mp (hClose q.2 hCyl)).1
    refine ⟨hSource,hBase,?_,?_⟩
    · linarith only [hHeight,hDiff,hLow]
    · linarith only [hHeight,hUp]
  right
  rcases hq with hOutside | hFront
  · have ho := hOutside
    rw [nativeRadialOutsideRoom_eq_positive_nativeGlobalEnergy S L C lam hlam R hR hRoom b Rstar hb hRs p] at ho
    have hE := ho.2.2
    unfold nativeGlobalEnergy at hE
    rw [real_inner_self_eq_norm_sq] at hE
    have hSq : (referenceRadius b Rstar p L q.2)^2<‖(nativeVelocityInverse S L C lam R q).2‖^2 := by linarith only [hE]
    have hLow := ((sq_lt_sq₀ (referenceRadius_pos b Rstar p L q.2 hb hRs).le (norm_nonneg _)).mp hSq).le
    have hUp : ‖(nativeVelocityInverse S L C lam R q).2‖≤referenceRadius c Rstar p L q.2 := by
      by_contra hn
      have hgt : referenceRadius c Rstar p L q.2<‖(nativeVelocityInverse S L C lam R q).2‖ := lt_of_not_ge hn
      have hs := (sq_lt_sq₀ (referenceRadius_pos c Rstar p L q.2 hc hRs).le (norm_nonneg _)).mpr hgt
      apply hOld
      rw [nativeRadialOutsideRoom_eq_positive_nativeGlobalEnergy S L C lam hlam R hR hRoom c Rstar hc hRs p]
      refine ⟨ho.1,ho.2.1,?_⟩
      unfold nativeGlobalEnergy
      rw [real_inner_self_eq_norm_sq]
      nlinarith only [hs]
    exact conclude ho.1 (interior_subset ho.2.1) hLow hUp
  · have hN := nativeSphereFront_subset_nativeNormalImage S L C lam hlam R hR hRoom b Rstar hb hRs p hRadiusB hFront
    have hNorm := nativeVelocityInverse_norm_on_nativeSphereFront S L C lam hlam R hR hRoom b Rstar p hb hRs hRadiusB q hFront
    have hCyl : q.2 ∈ cylinder := by
      obtain ⟨a,ha,hAq⟩ := hFront
      have hy : a.1=q.2 := congrArg Prod.snd hAq
      exact hy ▸ ha.1
    have hLow : referenceRadius b Rstar p L q.2≤‖(nativeVelocityInverse S L C lam R q).2‖ := hNorm.symm.le
    have hUp : ‖(nativeVelocityInverse S L C lam R q).2‖≤referenceRadius c Rstar p L q.2 := by
      rw [hNorm]
      exact referenceRadius_mono_delta b c Rstar p L q.2 hb hbc hRs.le
    exact conclude hN hCyl hLow hUp

/-- The SAME genuine output domain covers the new strict outside AND entire zero front through its actual compact-level slab. -/
theorem native_new_level_covered_of_actual_slab
    (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L)
    (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) C.dilationCeiling)
    (R : ℝ) (hR : 0<R) (hRoom : R<C.radiusCeiling)
    (b c Rstar : ℝ) (p : ℕ) (hb : 0<b) (hc : 0<c) (hbc : b≤c) (hRs : 0<Rstar)
    (hRadiusB : ∀ y ∈ cylinder, referenceRadius b Rstar p L y<R)
    (w : ℝ) (hw : 0<w)
    (hClose : ∀ y ∈ cylinder, |referenceRadius b Rstar p L y-referenceRadius c Rstar p L y|<w)
    (U : Set (R3 × R3)) (hOld : nativeRadialOutsideRoom S L C lam R c Rstar p ⊆ U)
    (V : Set (R3 × sphere (0 : R3) 1)) (hBase : cylinder ×ˢ univ ⊆ V)
    (hSlab : MapsTo (nativeEnergyRadialChart S L C lam hlam R hR hRoom c Rstar p hc hRs).symm (V ×ˢ Ioo (-w) w) U) :
    nativeRadialOutsideRoom S L C lam R b Rstar p ∪ nativeSphereFront S L C lam b Rstar p ⊆ U := by
  let e := nativeEnergyRadialChart S L C lam hlam R hR hRoom c Rstar p hc hRs
  intro q hq
  rcases native_new_level_mem_old_outside_or_actual_slab S L C lam hlam R hR hRoom b c Rstar p hb hc hbc hRs hRadiusB w hClose q hq with ho | hs
  · exact hOld ho
  · have hInside : e q ∈ V ×ˢ Ioo (-w) w := ⟨hBase hs.2.1,hs.2.2.1,hs.2.2.2.trans_lt hw⟩
    have hh := hSlab hInside
    change e.symm (e q) ∈ U at hh
    rw [e.left_inv hs.1] at hh
    exact hh

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
