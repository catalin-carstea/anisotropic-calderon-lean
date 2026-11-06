import Calderon.MixedKernelConstruction.MixedKernelNativeGlobalVelocityRoom
import Calderon.MixedKernelConstruction.MixedKernelSmoothInverseOnRoom
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter ConnectionError ConformalDepth ActualScalarPrincipalAdjoint
open scoped ContDiff Topology InnerProductSpace
local instance : CompleteSpace R3 := FiniteDimensional.complete ℝ R3
local instance : CompleteSpace (R3 × R3) := FiniteDimensional.complete ℝ (R3 × R3)

/-- The SAME cover's genuine open velocity source. -/
def nativeNormalVelocityRoom (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L) (R : ℝ) : Set (R3 × R3) :=
  nativeCoverCenterRoom S L C ×ˢ ball (0 : R3) R

theorem isOpen_nativeNormalVelocityRoom (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L) (R : ℝ) :
    IsOpen (nativeNormalVelocityRoom S L C R) := (isOpen_nativeCoverCenterRoom S L C).prod isOpen_ball

/-- The actual physical image of that exact common source. -/
def nativeNormalImage (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L) (lam R : ℝ) : Set (R3 × R3) :=
  nativeVelocityPair S L C lam R '' nativeNormalVelocityRoom S L C R

theorem isOpen_nativeNormalImage
    (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L)
    (lam : ℝ) (hlam : lam∈Icc (0 : ℝ) C.dilationCeiling)
    (R : ℝ) (hR : 0<R) (hRoom : R<C.radiusCeiling) :
    IsOpen (nativeNormalImage S L C lam R) :=
  isOpen_nativeVelocityPair_image S L C lam hlam R hR hRoom _
    (isOpen_nativeNormalVelocityRoom S L C R) (fun _ h => h)

/-- The coherent map is genuinely equal to a fixed original packet on a full neighborhood. -/
theorem nativeVelocityPair_eventuallyEq_packet
    (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L)
    (lam : ℝ) (hlam : lam∈Icc (0 : ℝ) C.dilationCeiling)
    (R : ℝ) (hR : 0<R) (hRoom : R<C.radiusCeiling)
    (i : Fin C.count) (a : R3 × R3)
    (ha : a∈(C.packet i).centers ×ˢ ball (0 : R3) R) :
    nativeVelocityPair S L C lam R =ᶠ[𝓝 a] packetVelocityPair S L (C.packet i) lam R := by
  have hN := ((C.packet i).centers_open.prod isOpen_ball).mem_nhds ha
  filter_upwards [hN] with b hb
  exact nativeVelocityPair_eq_packet S L C lam hlam R hR hRoom i b.1 hb.1 b.2
    (by simpa only [mem_ball,dist_zero_right] using hb.2)

/-- The ACTUAL coherent map's derivative is invertible throughout its actual open source. -/
theorem nativeVelocityPair_derivative_isInvertible
    (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L)
    (lam : ℝ) (hlam : lam∈Icc (0 : ℝ) C.dilationCeiling)
    (R : ℝ) (hR : 0<R) (hRoom : R<C.radiusCeiling)
    (a : R3 × R3) (ha : a∈nativeNormalVelocityRoom S L C R) :
    (fderiv ℝ (nativeVelocityPair S L C lam R) a).IsInvertible := by
  obtain ⟨i,hi⟩ := mem_iUnion.mp ha.1
  have hEq := nativeVelocityPair_eventuallyEq_packet S L C lam hlam R hR hRoom i a ⟨hi,ha.2⟩
  rw [hEq.fderiv_eq]
  exact packetVelocityPair_derivative_isInvertible S L (C.packet i) lam
    ⟨hlam.1,hlam.2.trans C.dilation_le_one⟩ R hR (hRoom.le.trans (C.radius_room i).le)
    a.1 hi a.2 (by simpa only [mem_ball,dist_zero_right] using ha.2)

/-- The actual unique inverse, with arbitrary values outside the original normal image. -/
def nativeVelocityInverse (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L) (lam R : ℝ) :
    (R3 × R3) → R3 × R3 :=
  Function.invFunOn (nativeVelocityPair S L C lam R) (nativeNormalVelocityRoom S L C R)

theorem nativeVelocityInverse_mem_right
    (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L) (lam R : ℝ)
    (q : R3 × R3) (hq : q∈nativeNormalImage S L C lam R) :
    nativeVelocityInverse S L C lam R q∈nativeNormalVelocityRoom S L C R ∧
      nativeVelocityPair S L C lam R (nativeVelocityInverse S L C lam R q)=q :=
  Function.invFunOn_pos hq

theorem nativeVelocityInverse_left
    (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L)
    (lam : ℝ) (hlam : lam∈Icc (0 : ℝ) C.dilationCeiling)
    (R : ℝ) (hR : 0<R) (hRoom : R<C.radiusCeiling)
    (a : R3 × R3) (ha : a∈nativeNormalVelocityRoom S L C R) :
    nativeVelocityInverse S L C lam R (nativeVelocityPair S L C lam R a)=a :=
  (nativeVelocityPair_injOn S L C lam hlam R hR hRoom).leftInvOn_invFunOn ha

/-- The inverse's smoothness is proved on the whole genuine physical image, without an extension premise. -/
theorem contDiffOn_nativeVelocityInverse
    (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L)
    (lam : ℝ) (hlam : lam∈Icc (0 : ℝ) C.dilationCeiling)
    (R : ℝ) (hR : 0<R) (hRoom : R<C.radiusCeiling) :
    ContDiffOn ℝ ∞ (nativeVelocityInverse S L C lam R) (nativeNormalImage S L C lam R) :=
  contDiffOn_invFunOn_of_actual_derivative_isInvertible _ _
    (isOpen_nativeNormalVelocityRoom S L C R) (contDiffOn_nativeVelocityPair S L C lam hlam R hR hRoom)
    (nativeVelocityPair_injOn S L C lam hlam R hR hRoom)
    (fun a ha => nativeVelocityPair_derivative_isInvertible S L C lam hlam R hR hRoom a ha)

/-- The inverse's center is exactly the physical second coordinate. -/
theorem nativeVelocityInverse_fst
    (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L) (lam R : ℝ)
    (q : R3 × R3) (hq : q∈nativeNormalImage S L C lam R) :
    (nativeVelocityInverse S L C lam R q).1=q.2 := by
  have hh := congrArg Prod.snd (nativeVelocityInverse_mem_right S L C lam R q hq).2
  exact hh

/-- One actual global energy, built from the SAME native inverse and ORIGINAL radius. -/
def nativeGlobalEnergy (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L)
    (lam R delta Rstar : ℝ) (p : ℕ) (q : R3 × R3) : ℝ :=
  (⟪(nativeVelocityInverse S L C lam R q).2,(nativeVelocityInverse S L C lam R q).2⟫_ℝ-
    (referenceRadius delta Rstar p L q.2)^2)/2

theorem contDiffOn_nativeGlobalEnergy
    (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L)
    (lam : ℝ) (hlam : lam∈Icc (0 : ℝ) C.dilationCeiling)
    (R : ℝ) (hR : 0<R) (hRoom : R<C.radiusCeiling)
    (delta Rstar : ℝ) (hd : 0<delta) (hRs : 0<Rstar) (p : ℕ) :
    ContDiffOn ℝ ∞ (nativeGlobalEnergy S L C lam R delta Rstar p) (nativeNormalImage S L C lam R) := by
  have hV := (contDiffOn_nativeVelocityInverse S L C lam hlam R hR hRoom).snd
  have hr : ContDiff ℝ ∞ (fun q : R3 × R3 => referenceRadius delta Rstar p L q.2) :=
    (contDiff_referenceRadius_actual delta Rstar p L hd hRs).comp contDiff_snd
  exact ((ContDiffOn.inner ℝ hV hV).sub (hr.pow 2).contDiffOn).div_const 2

/-- Exact energy evaluation on every actual velocity source point. -/
theorem nativeGlobalEnergy_on_velocity_pair
    (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L)
    (lam : ℝ) (hlam : lam∈Icc (0 : ℝ) C.dilationCeiling)
    (R : ℝ) (hR : 0<R) (hRoom : R<C.radiusCeiling)
    (delta Rstar : ℝ) (p : ℕ) (a : R3 × R3) (ha : a∈nativeNormalVelocityRoom S L C R) :
    nativeGlobalEnergy S L C lam R delta Rstar p (nativeVelocityPair S L C lam R a)=
      (⟪a.2,a.2⟫_ℝ-(referenceRadius delta Rstar p L a.1)^2)/2 := by
  unfold nativeGlobalEnergy
  rw [nativeVelocityInverse_left S L C lam hlam R hR hRoom a ha]
  rfl

/-- Genuine rescaling on an OPEN angular room, not only on the unit sphere. -/
theorem packetEndpoint_pair_eq_nativeVelocityPair_of_velocity_lt
    (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L)
    (lam : ℝ) (hlam : lam∈Icc (0 : ℝ) C.dilationCeiling)
    (R : ℝ) (hR : 0<R) (hRoom : R<C.radiusCeiling)
    (i : Fin C.count) (y : R3) (hy : y∈(C.packet i).centers)
    (r : ℝ) (w : R3) (hu : ‖r • w‖<R) :
    (packetEndpoint S L (C.packet i) lam y r w,y)=nativeVelocityPair S L C lam R (y,r • w) := by
  rw [nativeVelocityPair_eq_packet S L C lam hlam R hR hRoom i y hy (r • w) hu]
  change (packetEndpoint S L (C.packet i) lam y r w,y)=
    (packetEndpoint S L (C.packet i) lam y R (R⁻¹ • (r • w)),y)
  rw [packetEndpoint_radius_rescaling S L (C.packet i) lam y r R hR.ne' w]
  congr 2
  rw [smul_smul,div_eq_mul_inv,mul_comm r R⁻¹]

/-- The SAME global phase has the exact fixed-radius family identity near every native point. -/
theorem nativeGlobalEnergy_at_packetEndpoint
    (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L)
    (lam : ℝ) (hlam : lam∈Icc (0 : ℝ) C.dilationCeiling)
    (R : ℝ) (hR : 0<R) (hRoom : R<C.radiusCeiling)
    (delta Rstar : ℝ) (p : ℕ) (i : Fin C.count) (y : R3) (hy : y∈(C.packet i).centers)
    (r : ℝ) (w : R3) (hu : ‖r • w‖<R) :
    nativeGlobalEnergy S L C lam R delta Rstar p (packetEndpoint S L (C.packet i) lam y r w,y)=
      (r^2*⟪w,w⟫_ℝ-(referenceRadius delta Rstar p L y)^2)/2 := by
  rw [packetEndpoint_pair_eq_nativeVelocityPair_of_velocity_lt S L C lam hlam R hR hRoom i y hy r w hu,
    nativeGlobalEnergy_on_velocity_pair S L C lam hlam R hR hRoom delta Rstar p (y,r • w)
      ⟨mem_iUnion.mpr ⟨i,hy⟩,by simpa only [mem_ball,dist_zero_right] using hu⟩]
  rw [real_inner_smul_left,real_inner_smul_right]
  ring

/-- The entire original compact sphere front is inside the energy's actual smooth domain. -/
theorem nativeSphereFront_subset_nativeNormalImage
    (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L)
    (lam : ℝ) (hlam : lam∈Icc (0 : ℝ) C.dilationCeiling)
    (R : ℝ) (hR : 0<R) (hRoom : R<C.radiusCeiling)
    (delta Rstar : ℝ) (hd : 0<delta) (hRs : 0<Rstar) (p : ℕ)
    (hRadius : ∀ y∈cylinder, referenceRadius delta Rstar p L y<R) :
    nativeSphereFront S L C lam delta Rstar p⊆nativeNormalImage S L C lam R :=
  nativeSphereFront_subset_nativeVelocityImage S L C lam hlam R hR hRoom delta Rstar hd hRs p hRadius

/-- The ONE actual global energy vanishes on the WHOLE original front, including cylinder boundaries. -/
theorem nativeGlobalEnergy_zero_on_nativeSphereFront
    (S : KnownSideSourceData) (L : ℝ) (C : NativeNormalCover S L)
    (lam : ℝ) (hlam : lam∈Icc (0 : ℝ) C.dilationCeiling)
    (R : ℝ) (hR : 0<R) (hRoom : R<C.radiusCeiling)
    (delta Rstar : ℝ) (hd : 0<delta) (hRs : 0<Rstar) (p : ℕ)
    (hRadius : ∀ y∈cylinder, referenceRadius delta Rstar p L y<R) :
    ∀ q∈nativeSphereFront S L C lam delta Rstar p, nativeGlobalEnergy S L C lam R delta Rstar p q=0 := by
  rintro q ⟨a,ha,rfl⟩
  obtain ⟨i,hi⟩ := C.covers_cylinder a.1 ha.1
  let r := referenceRadius delta Rstar p L a.1
  have hr : 0<r := referenceRadius_pos delta Rstar p L a.1 hd hRs
  have hz : ‖a.2‖=1 := by simpa only [mem_sphere,dist_zero_right] using ha.2
  have hu : ‖r • a.2‖<R := by
    simpa only [norm_smul,Real.norm_eq_abs,abs_of_pos hr,hz,mul_one] using hRadius a.1 ha.1
  have hzClosed : a.2∈closedBall (0 : R3) 2 := by simp only [mem_closedBall,dist_zero_right,hz];norm_num
  change nativeGlobalEnergy S L C lam R delta Rstar p (nativeCoverEndpoint S L C lam ((a.1,r),a.2),a.1)=0
  rw [nativeCoverEndpoint_eq_packet S L C lam hlam i a.1 hi r hr ((hRadius a.1 ha.1).trans hRoom) a.2 hzClosed]
  rw [nativeGlobalEnergy_at_packetEndpoint S L C lam hlam R hR hRoom delta Rstar p i a.1 hi r a.2 hu,
    real_inner_self_eq_norm_sq,hz]
  change (r^2*1^2-r^2)/2=0
  ring

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
