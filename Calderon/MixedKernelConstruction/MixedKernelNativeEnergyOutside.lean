import Calderon.MixedKernelConstruction.MixedKernelNativeGlobalEnergy
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter ConnectionError ConformalDepth
open scoped Topology InnerProductSpace

/-- The positive side of the ONE actual global energy is exactly the original radial outside image. -/
theorem nativeRadialOutsideRoom_eq_positive_nativeGlobalEnergy
    (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L)
    (lam : ℝ) (hlam : lam∈Icc (0 : ℝ) C.dilationCeiling)
    (R : ℝ) (hR : 0<R) (hRoom : R<C.radiusCeiling)
    (delta Rstar : ℝ) (hd : 0<delta) (hRs : 0<Rstar) (p : ℕ) :
    nativeRadialOutsideRoom S L C lam R delta Rstar p=
      {q : R3 × R3 | q∈nativeNormalImage S L C lam R ∧ q.2∈interior cylinder ∧
        0<nativeGlobalEnergy S L C lam R delta Rstar p q} := by
  ext q
  constructor
  · rintro ⟨a,ha,rfl⟩
    have hA : a∈nativeNormalVelocityRoom S L C R :=
      ⟨ha.1.1,by simpa only [mem_ball,dist_zero_right] using ha.2.2⟩
    refine ⟨⟨a,hA,rfl⟩,ha.1.2,?_⟩
    rw [nativeGlobalEnergy_on_velocity_pair S L C lam hlam R hR hRoom delta Rstar p a hA,
      real_inner_self_eq_norm_sq]
    have hr := referenceRadius_pos delta Rstar p L a.1 hd hRs
    have hSq := (sq_lt_sq₀ hr.le (norm_nonneg a.2)).mpr ha.2.1
    nlinarith only [hSq]
  · rintro ⟨hq,hcyl,hE⟩
    let a := nativeVelocityInverse S L C lam R q
    obtain ⟨hA,hRight⟩ := nativeVelocityInverse_mem_right S L C lam R q hq
    change a∈nativeNormalVelocityRoom S L C R at hA
    change nativeVelocityPair S L C lam R a=q at hRight
    have hy : a.1=q.2 := nativeVelocityInverse_fst S L C lam R q hq
    have hEnergy := nativeGlobalEnergy_on_velocity_pair S L C lam hlam R hR hRoom delta Rstar p a hA
    rw [hRight,real_inner_self_eq_norm_sq] at hEnergy
    have hr := referenceRadius_pos delta Rstar p L a.1 hd hRs
    have hLower : referenceRadius delta Rstar p L a.1<‖a.2‖ := by
      have hn := norm_nonneg a.2
      apply (sq_lt_sq₀ hr.le hn).mp
      nlinarith only [hEnergy,hE]
    refine ⟨a,⟨⟨hA.1,by rw [hy];exact hcyl⟩,hLower,?_⟩,hRight⟩
    simpa only [mem_ball,dist_zero_right] using hA.2

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
