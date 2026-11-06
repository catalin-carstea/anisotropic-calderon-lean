import Calderon.MixedKernelConstruction.MixedKernelSmoothPacketInverse
set_option autoImplicit false
set_option maxHeartbeats 200000
noncomputable section
namespace OAI.AnisotropicCalderon.MixedKernelConstructionTask
open Set Metric Filter ConnectionError
open scoped ContDiff Topology InnerProductSpace

local instance : CompleteSpace R3 := FiniteDimensional.complete ℝ R3
local instance : CompleteSpace (R3 × R3) := FiniteDimensional.complete ℝ (R3 × R3)

/-- The actual pair map has an invertible derivative whenever its vertical endpoint derivative is injective. -/
theorem endpoint_pair_derivative_isInvertible
    (f : R3 × R3 → R3) (a : R3 × R3) (hf : DifferentiableAt ℝ f a)
    (hVert : Function.Injective ((fderiv ℝ f a).comp (ContinuousLinearMap.inr ℝ R3 R3))) :
    (fderiv ℝ (fun b : R3 × R3 => (f b,b.1)) a).IsInvertible := by
  let A := fderiv ℝ f a
  let DT := A.prod (ContinuousLinearMap.fst ℝ R3 R3)
  have hd : HasFDerivAt (fun b : R3 × R3 => (f b,b.1)) DT a :=
    hf.hasFDerivAt.prodMk (hasFDerivAt_fst (𝕜 := ℝ) (p := a))
  have hInject : Function.Injective DT := by
    intro u v h
    change (A u,u.1)=(A v,v.1) at h
    have hy : u.1=v.1 := congrArg Prod.snd h
    have hA : A u=A v := congrArg Prod.fst h
    have hSplit (b : R3 × R3) : A b =
        (A.comp (ContinuousLinearMap.inl ℝ R3 R3)) b.1+
        (A.comp (ContinuousLinearMap.inr ℝ R3 R3)) b.2 :=
      (A.comp_inl_add_comp_inr b).symm
    rw [hSplit u,hSplit v,hy] at hA
    exact Prod.ext hy (hVert (add_left_cancel hA))
  have hb : Function.Bijective DT.toLinearMap := ⟨hInject,DT.toLinearMap.surjective_of_injective hInject⟩
  rw [hd.fderiv]
  refine ⟨(LinearEquiv.ofBijective DT.toLinearMap hb).toContinuousLinearEquiv,?_⟩
  apply ContinuousLinearMap.ext
  intro x
  rfl

/-- A genuine smooth inverse at each parameter point makes the image of an open room open. -/
theorem isOpen_image_of_actual_invertible_derivative
    (F : (R3 × R3) → R3 × R3) (hf : ContDiff ℝ ∞ F)
    (A : Set (R3 × R3)) (hA : IsOpen A)
    (hD : ∀ a ∈ A, (fderiv ℝ F a).IsInvertible) : IsOpen (F '' A) := by
  rw [isOpen_iff_mem_nhds]
  intro q hq
  obtain ⟨a,ha,rfl⟩ := hq
  obtain ⟨G,V,hV,hbase,hG,hGa,hRight,_⟩ := exists_open_smooth_local_inverse F hf a (hD a ha)
  have hc : ContinuousAt G (F a) := (hG.contDiffAt (hV.mem_nhds hbase)).continuousAt
  have hGmem : G (F a) ∈ A := by rw [hGa];exact ha
  have hGA : ∀ᶠ q in 𝓝 (F a), G q ∈ A := hc.eventually (hA.mem_nhds hGmem)
  filter_upwards [hV.mem_nhds hbase,hGA] with q hqV hqA
  exact ⟨G q,hqA,hRight q hqV⟩

/-- The derivative of the ACTUAL packet pair map is invertible on its full closed angular room. -/
theorem packet_normal_pair_derivative_isInvertible
    (S : KnownSideSourceData) (L : ℝ) (P : NativeNormalPacket S L)
    (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) 1)
    (r : ℝ) (hrpos : 0 < r) (hr : r ≤ 4*P.rho)
    (y : R3) (hy : y ∈ P.centers) (z : R3) (hz : z ∈ closedBall (0 : R3) 2) :
    (fderiv ℝ (fun a : R3 × R3 => (packetEndpoint S L P lam a.1 r a.2,a.1)) (y,z)).IsInvertible := by
  let f : R3 × R3 → R3 := fun a => packetEndpoint S L P lam a.1 r a.2
  have hEnd : ConformalReferenceGeodesicEndpointData S.g1 L P.y0 P.Phi P.B := P.native_data.1.1.1
  have hTheta : ContDiff ℝ ∞ (fun a : ℝ × (R3 × R3) => (P.Phi a.1 a.2 1).1) := hEnd.2.2.2.2.2.2.2.1
  have hf : ContDiff ℝ ∞ f := by
    exact (contDiff_referenceFramedPhysicalEndpoint S.g1 S.g1_admissible L P.Phi hTheta).comp
      (contDiff_const.prodMk ((contDiff_fst.prodMk contDiff_const).prodMk contDiff_snd))
  let a : R3 × R3 := (y,z)
  apply endpoint_pair_derivative_isInvertible f a (hf.differentiable (by simp) a)
  have hInv := packet_normalizedJacobian_isInvertible S L P lam hlam y hy r
    (by rw [abs_of_pos hrpos];exact hr) z hz
  let J := referenceFramedNormalizedJacobian S.g1 L P.Phi (lam,((a.1,r),a.2))
  have hs : HasFDerivAt (fun w => f (a.1,w)) (r • J) a.2 :=
    hasFDerivAt_framedScaledEndpoint_slice (fun b => (P.Phi lam b 1).1)
      (fun Y => conformalReferenceGramFrameOperatorJoint S.g1 L (lam,Y))
      (hTheta.comp (contDiff_const.prodMk contDiff_id)) a.1 a.2 r
  have hv := (hf.differentiable (by simp) a).hasFDerivAt.comp a.2 (hasFDerivAt_prodMk_right a.1 a.2)
  have heq : (fderiv ℝ f a).comp (ContinuousLinearMap.inr ℝ R3 R3) = r • J := hv.unique hs
  rw [heq]
  intro U V hUV
  have hCancel : J U=J V := by
    change r • J U=r • J V at hUV
    exact smul_right_injective (M := R3) hrpos.ne' hUV
  have h := congrArg (ContinuousLinearMap.inverse J) hCancel
  have hi (X : R3) : ContinuousLinearMap.inverse J (J X)=X := by
    have hh := congrArg (fun A : R3 →L[ℝ] R3 => A X) hInv.inverse_comp_self
    simpa only [ContinuousLinearMap.comp_apply,ContinuousLinearMap.id_apply] using hh
  simpa only [hi] using h


/-- The actual native normal pair image of the full open center/angular room is open. -/
theorem isOpen_packet_normal_pair_image
    (S : KnownSideSourceData) (L : ℝ) (P : NativeNormalPacket S L)
    (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) 1)
    (r : ℝ) (hrpos : 0 < r) (hr : r ≤ 4*P.rho) :
    IsOpen ((fun a : R3 × R3 => (packetEndpoint S L P lam a.1 r a.2,a.1)) ''
      (P.centers ×ˢ ball (0 : R3) 2)) := by
  let f : R3 × R3 → R3 := fun a => packetEndpoint S L P lam a.1 r a.2
  have hEnd : ConformalReferenceGeodesicEndpointData S.g1 L P.y0 P.Phi P.B := P.native_data.1.1.1
  have hTheta : ContDiff ℝ ∞ (fun a : ℝ × (R3 × R3) => (P.Phi a.1 a.2 1).1) := hEnd.2.2.2.2.2.2.2.1
  have hf : ContDiff ℝ ∞ f := by
    exact (contDiff_referenceFramedPhysicalEndpoint S.g1 S.g1_admissible L P.Phi hTheta).comp
      (contDiff_const.prodMk ((contDiff_fst.prodMk contDiff_const).prodMk contDiff_snd))
  apply isOpen_image_of_actual_invertible_derivative (fun a : R3 × R3 => (f a,a.1))
    (hf.prodMk contDiff_fst) _ (P.centers_open.prod isOpen_ball)
  intro a ha
  exact packet_normal_pair_derivative_isInvertible S L P lam hlam r hrpos hr a.1 ha.1 a.2
    (ball_subset_closedBall ha.2)

/-- Equality of pullback germs through a genuine local inverse gives equality of physical germs. -/
theorem eventuallyEq_of_comp_of_actual_local_inverse
    (F : (R3 × R3) → R3 × R3) (hF : ContDiff ℝ ∞ F) (a : R3 × R3)
    (hD : (fderiv ℝ F a).IsInvertible) (u v : R3 × R3 → ℝ)
    (hComp : (fun b => u (F b)) =ᶠ[𝓝 a] (fun b => v (F b))) :
    u =ᶠ[𝓝 (F a)] v := by
  obtain ⟨G,V,hV,hbase,hG,hGa,hRight,_⟩ := exists_open_smooth_local_inverse F hF a hD
  have hc : ContinuousAt G (F a) := (hG.contDiffAt (hV.mem_nhds hbase)).continuousAt
  have hc' : Tendsto G (𝓝 (F a)) (𝓝 a) := by
    have hh : Tendsto G (𝓝 (F a)) (𝓝 (G (F a))) := hc
    simpa only [hGa] using hh
  have hEq := hc'.eventually hComp
  filter_upwards [hEq,hV.mem_nhds hbase] with q hq hqV
  simpa only [hRight q hqV] using hq

/-- Any two native phases with the same genuine family identity have the SAME physical germ. -/
theorem packet_phases_eventuallyEq_of_family_identity
    (S : KnownSideSourceData) (L : ℝ) (P : NativeNormalPacket S L)
    (lam : ℝ) (hlam : lam ∈ Icc (0 : ℝ) 1)
    (r : ℝ) (hrpos : 0 < r) (hr : r ≤ 4*P.rho)
    (y : R3) (hy : y ∈ P.centers) (z : R3) (hz : z ∈ closedBall (0 : R3) 2)
    (rho tau : R3 × R3 → ℝ)
    (hRho : ∀ᶠ b : R3 × R3 in 𝓝 (y,z),
      rho (packetEndpoint S L P lam b.1 r b.2,b.1)=(⟪b.2,b.2⟫_ℝ-1)/2)
    (hTau : ∀ᶠ b : R3 × R3 in 𝓝 (y,z),
      tau (packetEndpoint S L P lam b.1 r b.2,b.1)=(⟪b.2,b.2⟫_ℝ-1)/2) :
    rho =ᶠ[𝓝 (packetEndpoint S L P lam y r z,y)] tau := by
  let N : (R3 × R3) → R3 × R3 := fun a => (packetEndpoint S L P lam a.1 r a.2,a.1)
  have hEnd : ConformalReferenceGeodesicEndpointData S.g1 L P.y0 P.Phi P.B := P.native_data.1.1.1
  have hTheta : ContDiff ℝ ∞ (fun a : ℝ × (R3 × R3) => (P.Phi a.1 a.2 1).1) := hEnd.2.2.2.2.2.2.2.1
  have hf : ContDiff ℝ ∞ (fun a : R3 × R3 => packetEndpoint S L P lam a.1 r a.2) :=
    (contDiff_referenceFramedPhysicalEndpoint S.g1 S.g1_admissible L P.Phi hTheta).comp
      (contDiff_const.prodMk ((contDiff_fst.prodMk contDiff_const).prodMk contDiff_snd))
  have hN : ContDiff ℝ ∞ N := hf.prodMk contDiff_fst
  have hComp : (fun b => rho (N b)) =ᶠ[𝓝 (y,z)] (fun b => tau (N b)) := by
    filter_upwards [hRho,hTau] with b hb hc
    exact hb.trans hc.symm
  exact eventuallyEq_of_comp_of_actual_local_inverse N hN (y,z)
    (packet_normal_pair_derivative_isInvertible S L P lam hlam r hrpos hr y hy z hz)
    rho tau hComp

end OAI.AnisotropicCalderon.MixedKernelConstructionTask
end
