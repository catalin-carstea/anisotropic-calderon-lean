import MixedKernelNativeRadialCoordinates
import MixedKernelPacketEndpointBounds
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter ConnectionError ConformalDepth
open scoped ContDiff Topology InnerProductSpace

/-- One genuine linear separation cap holds on the ENTIRE original nonzero native normal room. -/
theorem exists_native_normal_room_separation_upper
    (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L) :
    ∃ R0 K : ℝ, 0<R0 ∧ R0<C.radiusCeiling ∧ 0<K ∧
      ∀ R : ℝ, 0<R → R≤R0 → ∀ lam ∈ Icc (0 : ℝ) C.dilationCeiling,
      ∀ q ∈ nativeNormalImage S L C lam R,
        (nativeVelocityInverse S L C lam R q).2≠0 →
        ‖q.1-q.2‖≤K*‖(nativeVelocityInverse S L C lam R q).2‖ ∧ ‖q.1-q.2‖<K*R := by
  classical
  choose rN cN CN hrN hrRhoN hrOneN hcN hCN HN using fun i : Fin C.count =>
    exists_packet_endpoint_linear_bounds S L (C.packet i)
  let i0 : Fin C.count := ⟨0,C.count_positive⟩
  let Radii : Finset ℝ := Finset.univ.image rN
  let Coeff : Finset ℝ := Finset.univ.image CN
  have hRadii : Radii.Nonempty := ⟨rN i0,Finset.mem_image.mpr ⟨i0,Finset.mem_univ i0,rfl⟩⟩
  have hCoeff : Coeff.Nonempty := ⟨CN i0,Finset.mem_image.mpr ⟨i0,Finset.mem_univ i0,rfl⟩⟩
  let rMin := Radii.min' hRadii
  let K := Coeff.max' hCoeff
  have hrMin : 0<rMin := by
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp (Finset.min'_mem Radii hRadii)
    change 0<Radii.min' hRadii
    rw [←hi]
    exact hrN i
  have hK : 0<K := by
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp (Finset.max'_mem Coeff hCoeff)
    change 0<Coeff.max' hCoeff
    rw [←hi]
    exact hCN i
  have hrAll (i : Fin C.count) : rMin≤rN i :=
    Finset.min'_le Radii (rN i) (Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩)
  have hKAll (i : Fin C.count) : CN i≤K :=
    Finset.le_max' Coeff (CN i) (Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩)
  let R0 := min (C.radiusCeiling/2) rMin
  have hR0 : 0<R0 := lt_min (by linarith [C.radius_positive]) hrMin
  have hRoom0 : R0<C.radiusCeiling :=
    (min_le_left _ _).trans_lt (by linarith [C.radius_positive])
  refine ⟨R0,K,hR0,hRoom0,hK,?_⟩
  intro R hR hRR lam hlam q hq hv
  have hRoom : R<C.radiusCeiling := hRR.trans_lt hRoom0
  let a := nativeVelocityInverse S L C lam R q
  obtain ⟨hA,hRight⟩ := nativeVelocityInverse_mem_right S L C lam R q hq
  change a ∈ nativeNormalVelocityRoom S L C R at hA
  change nativeVelocityPair S L C lam R a=q at hRight
  obtain ⟨i,hi⟩ := mem_iUnion.mp hA.1
  let P := C.packet i
  let r := ‖a.2‖
  have hr : 0<r := norm_pos_iff.mpr hv
  have hrR : r<R := by simpa only [mem_ball,dist_zero_right] using hA.2
  have hrN : r≤rN i := hrR.le.trans (hRR.trans ((min_le_right _ _).trans (hrAll i)))
  let z := r⁻¹ • a.2
  have hz : ‖z‖=1 := by
    dsimp only [z]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]
    change r⁻¹*r=1
    exact inv_mul_cancel₀ hr.ne'
  have hrz : r • z=a.2 := by
    dsimp only [z]
    rw [smul_smul,mul_inv_cancel₀ hr.ne',one_smul]
  have hPair := packetEndpoint_pair_eq_nativeVelocityPair S L C lam hlam R hR hRoom i a.1 hi r hr hrR z hz
  rw [hrz] at hPair
  have hQ : q=(packetEndpoint S L P lam a.1 r z,a.1) := (hPair.trans hRight).symm
  have hyRoom : ‖a.1-P.y0‖≤4*P.rho := (P.centers_room a.1 hi).1.le
  have hHigh := (HN i lam ⟨hlam.1,hlam.2.trans C.dilation_le_one⟩ a.1 hyRoom r ⟨hr.le,hrN⟩ z hz).2
  have hBound : ‖q.1-q.2‖≤K*r := by
    rw [hQ]
    exact hHigh.trans (mul_le_mul_of_nonneg_right (hKAll i) hr.le)
  exact ⟨hBound,hBound.trans_lt (mul_lt_mul_of_pos_left hrR hK)⟩

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
