import MixedKernelNativeRadialCoordinates
import MixedKernelPacketEndpointBounds
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter ConnectionError ConformalDepth
open scoped ContDiff Topology InnerProductSpace

/-- The SAME actual upward radial seed needs only the original known cross and one positive Euclidean separation range. -/
theorem exists_native_radial_seed_euclidean_cover_parameters
    (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L) :
    ∃ R0 c B : ℝ, 0 < R0 ∧ R0 < C.radiusCeiling ∧ 0 < c ∧ 0 < B ∧
      ∀ R : ℝ, 0 < R → R ≤ R0 → ∀ lam ∈ Icc (0 : ℝ) C.dilationCeiling,
      ∀ tail : ℝ, 0 < tail →
        nativeRadialSeedRoom S L C lam R tail ⊆ initialCross S lam ∪ fixedSeparationSet B (c*tail) := by
  classical
  choose rN cN CN hrN hrRhoN hrOneN hcN hCN HN using fun i : Fin C.count =>
    exists_packet_endpoint_linear_bounds S L (C.packet i)
  let i0 : Fin C.count := ⟨0,C.count_positive⟩
  let Radii : Finset ℝ := Finset.univ.image rN
  let Coeff : Finset ℝ := Finset.univ.image cN
  have hRadii : Radii.Nonempty := ⟨rN i0,Finset.mem_image.mpr ⟨i0,Finset.mem_univ i0,rfl⟩⟩
  have hCoeff : Coeff.Nonempty := ⟨cN i0,Finset.mem_image.mpr ⟨i0,Finset.mem_univ i0,rfl⟩⟩
  let rMin := Radii.min' hRadii
  let c := Coeff.min' hCoeff
  have hrMin : 0 < rMin := by
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp (Finset.min'_mem Radii hRadii)
    change 0<Radii.min' hRadii
    rw [←hi]
    exact hrN i
  have hc : 0 < c := by
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp (Finset.min'_mem Coeff hCoeff)
    change 0<Coeff.min' hCoeff
    rw [←hi]
    exact hcN i
  have hrAll (i : Fin C.count) : rMin ≤ rN i :=
    Finset.min'_le Radii (rN i) (Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩)
  have hcAll (i : Fin C.count) : c ≤ cN i :=
    Finset.min'_le Coeff (cN i) (Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩)
  let R0 := min (min 1 (C.radiusCeiling/2)) rMin
  have hR0 : 0 < R0 := lt_min (lt_min (by norm_num) (div_pos C.radius_positive (by norm_num))) hrMin
  have hR0One : R0 ≤ 1 := (min_le_left _ _).trans (min_le_left _ _)
  have hR0Room : R0 < C.radiusCeiling := by
    have hh : R0 ≤ C.radiusCeiling/2 := (min_le_left _ _).trans (min_le_right _ _)
    linarith [C.radius_positive]
  have hR0All (i : Fin C.count) : R0 ≤ rN i := (min_le_right _ _).trans (hrAll i)
  let bN (i : Fin C.count) := 1+‖(C.packet i).y0‖+4*(C.packet i).rho+CN i
  let Bounds : Finset ℝ := Finset.univ.image bN
  have hBounds : Bounds.Nonempty := ⟨bN i0,Finset.mem_image.mpr ⟨i0,Finset.mem_univ i0,rfl⟩⟩
  let B := Bounds.max' hBounds
  have hB : 0 < B := by
    obtain ⟨i,_,hi⟩ := Finset.mem_image.mp (Finset.max'_mem Bounds hBounds)
    have hh : 0 < bN i := by
      have hRhoPos : 0<(C.packet i).rho := (C.packet i).rho_positive
      have hCNPos : 0<CN i := hCN i
      dsimp only [bN]
      positivity
    change 0<Bounds.max' hBounds
    rw [←hi]
    exact hh
  have hBAll (i : Fin C.count) : bN i ≤ B :=
    Finset.le_max' Bounds (bN i) (Finset.mem_image.mpr ⟨i,Finset.mem_univ i,rfl⟩)
  refine ⟨R0,c,B,hR0,hR0Room,hc,hB,?_⟩
  intro R hR hRR0 lam hlam tail hTail q hq
  have hRoom : R < C.radiusCeiling := hRR0.trans_lt hR0Room
  have hOff := nativeNormalImage_mem_dilatedOffDiagonal_of_velocity_ne_zero S L C lam hlam R hR hRoom q hq.1 hq.2.1
  rcases hq.2.2 with hW | hFar
  · exact Or.inl ⟨hOff,Or.inr hW⟩
  right
  let a := nativeVelocityInverse S L C lam R q
  obtain ⟨hA,hRight⟩ := nativeVelocityInverse_mem_right S L C lam R q hq.1
  change a ∈ nativeNormalVelocityRoom S L C R at hA
  change nativeVelocityPair S L C lam R a = q at hRight
  obtain ⟨i,hi⟩ := mem_iUnion.mp hA.1
  let P := C.packet i
  let r := ‖a.2‖
  have hr : 0 < r := norm_pos_iff.mpr hq.2.1
  have hrR : r < R := by simpa only [mem_ball,dist_zero_right] using hA.2
  have hrN : r ≤ rN i := hrR.le.trans (hRR0.trans (hR0All i))
  have hr1 : r ≤ 1 := hrR.le.trans (hRR0.trans hR0One)
  let z := r⁻¹ • a.2
  have hz : ‖z‖ = 1 := by
    dsimp only [z]
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hr)]
    change r⁻¹*r = 1
    exact inv_mul_cancel₀ hr.ne'
  have hrz : r • z = a.2 := by
    dsimp only [z]
    rw [smul_smul,mul_inv_cancel₀ hr.ne',one_smul]
  have hPair := packetEndpoint_pair_eq_nativeVelocityPair S L C lam hlam R hR hRoom i a.1 hi r hr hrR z hz
  rw [hrz] at hPair
  have hQ : q = (packetEndpoint S L P lam a.1 r z,a.1) := (hPair.trans hRight).symm
  have hyRoom : ‖a.1-P.y0‖ ≤ 4*P.rho := (P.centers_room a.1 hi).1.le
  have hY : ‖q.2‖ ≤ ‖P.y0‖+4*P.rho := by
    rw [hQ]
    have hh := norm_add_le (a.1-P.y0) P.y0
    rw [sub_add_cancel] at hh
    linarith
  obtain ⟨hLow,hHigh⟩ := HN i lam ⟨hlam.1,hlam.2.trans C.dilation_le_one⟩ a.1 hyRoom r ⟨hr.le,hrN⟩ z hz
  have hDist : ‖q.1-q.2‖ = ‖packetEndpoint S L P lam a.1 r z-a.1‖ := by rw [hQ]
  have hUpper : ‖q.1-q.2‖ ≤ CN i := by
    rw [hDist]
    exact hHigh.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hr1 (hCN i).le)
  have hLower : c*r ≤ ‖q.1-q.2‖ := by
    rw [hDist]
    exact (mul_le_mul_of_nonneg_right (hcAll i) hr.le).trans hLow
  have hYB : ‖q.2‖ ≤ B := by
    have hh := hBAll i
    dsimp only [bN] at hh
    linarith [hCN i]
  have hXB : ‖q.1‖ ≤ B := by
    have hh := norm_add_le (q.1-q.2) q.2
    rw [sub_add_cancel] at hh
    have hbi := hBAll i
    dsimp only [bN] at hbi
    linarith
  have hFar' : tail < r := hFar
  exact ⟨hXB,hYB,(mul_lt_mul_of_pos_left hFar' hc).le.trans hLower⟩

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
