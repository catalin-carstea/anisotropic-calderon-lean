import Calderon.ConformalReferenceOperators
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Topology.Compactness.Compact
import Mathlib.Tactic

/-! Exact actual S10 local-operator caller. This extension is not asserted to be
an IsAdmissibleMetric: it preserves the actual local coefficients as germs and
feeds the genuine generic parameter geodesic endpoint construction. -/
set_option autoImplicit false
noncomputable section
open Set Metric Filter Topology
open scoped ContDiff InnerProductSpace
namespace OAI.AnisotropicCalderon.ConnectionError

theorem exists_contDiff_positive_operator_extension
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [FiniteDimensional ℝ P]
    (M : P × R3 → R3 →L[ℝ] R3) (O K : Set (P × R3))
    (hO : IsOpen O) (hK : IsCompact K) (hKO : K ⊆ O)
    (hM : ContDiffOn ℝ ∞ M O)
    (hSym : ∀ p ∈ O, ∀ X Y : R3, inner ℝ (M p X) Y = inner ℝ (M p Y) X)
    (hPos : ∀ p ∈ O, ∀ X : R3, X ≠ 0 → 0 < inner ℝ (M p X) X) :
    ∃ Mext : P × R3 → R3 →L[ℝ] R3,
      let Qext : P × R3 → R3 →L[ℝ] R3 := fun p => Ring.inverse (Mext p)
      ContDiff ℝ ∞ Mext ∧ ContDiff ℝ ∞ Qext ∧
      (∀ p, ∀ X Y : R3, inner ℝ (Mext p X) Y = inner ℝ (Mext p Y) X) ∧
      (∀ p, ∀ X : R3, X ≠ 0 → 0 < inner ℝ (Mext p X) X) ∧
      (∀ p, IsUnit (Mext p)) ∧
      (∀ p, ∀ X : R3, Mext p (Qext p X) = X ∧ Qext p (Mext p X) = X) ∧
      ∃ U : Set (P × R3), IsOpen U ∧ K ⊆ U ∧ U ⊆ O ∧
        (∀ p ∈ U, Mext =ᶠ[𝓝 p] M) ∧
        (∀ p ∈ U, Qext =ᶠ[𝓝 p] (fun q => Ring.inverse (M q)))
 := by
  classical
  have hRadii : ∀ c : K, ∃ r : ℝ, 0 < r ∧
      closedBall (c : P × R3) (2*r) ⊆ O := by
    intro c
    obtain ⟨d,hd,hdO⟩ := Metric.nhds_basis_closedBall.mem_iff.mp
      (hO.mem_nhds (hKO c.2))
    refine ⟨d/2,half_pos hd,?_⟩
    have he : 2*(d/2) = d := by ring
    simpa only [he] using hdO
  choose r hr hRoom using hRadii
  let chi : (c : K) → ContDiffBump (c : P × R3) := fun c =>
    ⟨r c,2*r c,hr c,by linarith only [hr c]⟩
  obtain ⟨F,hCover⟩ := hK.elim_finite_subcover
    (fun c : K => ball (c : P × R3) (r c))
    (fun _ => isOpen_ball) (by
      intro p hp
      exact mem_iUnion.mpr ⟨⟨p,hp⟩,mem_ball_self (hr ⟨p,hp⟩)⟩)
  let U : Set (P × R3) := ⋃ c ∈ F, ball (c : P × R3) (r c)
  let S : Set (P × R3) := ⋃ c ∈ F, closedBall (c : P × R3) (2*r c)
  have hUOpen : IsOpen U := isOpen_biUnion (fun c hc => isOpen_ball)
  have hKU : K ⊆ U := hCover
  have hSClosed : IsClosed S := isClosed_biUnion_finset (fun c hc => isClosed_closedBall)
  have hSO : S ⊆ O := by
    intro p hp
    obtain ⟨c,hc,hpBall⟩ := mem_iUnion₂.mp hp
    exact hRoom c hpBall
  have hUS : U ⊆ S := by
    intro p hp
    obtain ⟨c,hc,hpBall⟩ := mem_iUnion₂.mp hp
    have hRadius : r c ≤ 2*r c := by linarith only [hr c]
    have hOuter : p ∈ closedBall (c : P × R3) (2*r c) :=
      mem_closedBall.mpr ((mem_ball.mp hpBall).le.trans hRadius)
    exact mem_iUnion₂.mpr ⟨c,hc,hOuter⟩
  have hUO : U ⊆ O := hUS.trans hSO
  let beta : P × R3 → ℝ := fun p => 1-∏ c ∈ F, (1-chi c p)
  have hBetaSmooth : ContDiff ℝ ∞ beta :=
    contDiff_const.sub (contDiff_prod (fun c hc => contDiff_const.sub (chi c).contDiff))
  have hProdRange (T : Finset K) (p : P × R3) :
      0 ≤ ∏ c ∈ T, (1-chi c p) ∧ (∏ c ∈ T, (1-chi c p)) ≤ 1 := by
    induction T using Finset.induction_on with
    | empty => simp only [Finset.prod_empty,zero_le_one,le_refl,and_self]
    | @insert c T hc ih =>
      rw [Finset.prod_insert hc]
      have hNonneg : 0 ≤ 1-chi c p := sub_nonneg.mpr (chi c).le_one
      have hLe : 1-chi c p ≤ 1 := by linarith only [(chi c).nonneg (x := p)]
      refine ⟨mul_nonneg hNonneg ih.1,?_⟩
      calc
        (1-chi c p)*(∏ d ∈ T, (1-chi d p)) ≤
            1*(∏ d ∈ T, (1-chi d p)) := mul_le_mul_of_nonneg_right hLe ih.1
        _ ≤ 1 := by simpa only [one_mul] using ih.2
  have hBetaRange (p : P × R3) : 0 ≤ beta p ∧ beta p ≤ 1 := by
    change 0 ≤ 1-(∏ c ∈ F, (1-chi c p)) ∧ 1-(∏ c ∈ F, (1-chi c p)) ≤ 1
    constructor <;> linarith only [(hProdRange F p).1,(hProdRange F p).2]
  have hBetaOne (p : P × R3) (hp : p ∈ U) : beta p = 1 := by
    obtain ⟨c,hc,hpBall⟩ := mem_iUnion₂.mp hp
    have hChi : chi c p = 1 := (chi c).one_of_mem_closedBall (ball_subset_closedBall hpBall)
    have hZero : (∏ d ∈ F, (1-chi d p)) = 0 :=
      Finset.prod_eq_zero hc (by rw [hChi,sub_self])
    change 1-(∏ d ∈ F, (1-chi d p)) = 1
    rw [hZero,sub_zero]
  have hBetaZero (p : P × R3) (hp : p ∉ S) : beta p = 0 := by
    have hChi (c : K) (hc : c ∈ F) : chi c p = 0 := by
      have hNot : p ∉ closedBall (c : P × R3) (2*r c) := by
        intro hBall
        exact hp (mem_iUnion₂.mpr ⟨c,hc,hBall⟩)
      have hNotSupport : p ∉ tsupport (chi c) := by
        simpa only [(chi c).tsupport_eq] using hNot
      exact image_eq_zero_of_notMem_tsupport hNotSupport
    have hOne : (∏ c ∈ F, (1-chi c p)) = 1 := by
      apply Finset.prod_eq_one
      intro c hc
      rw [hChi c hc,sub_zero]
    change 1-(∏ c ∈ F, (1-chi c p)) = 0
    rw [hOne,sub_self]
  have hSupport : Function.support beta ⊆ S := by
    intro p hp
    change beta p ≠ 0 at hp
    by_contra hNot
    exact hp (hBetaZero p hNot)
  have hTS : tsupport beta ⊆ O :=
    (closure_minimal hSupport hSClosed).trans hSO
  have hFirstLocal : ContDiffOn ℝ ∞ (fun p => beta p • M p) O :=
    hBetaSmooth.contDiffOn.smul hM
  have hZeroMap (A : R3 →L[ℝ] R3) : (0 : ℝ) • A = 0 := by
    apply ContinuousLinearMap.ext
    intro X
    change (0 : ℝ) • (A X) = (0 : R3)
    exact zero_smul ℝ (A X)
  have hFirstZero : ContDiffOn ℝ ∞ (fun p => beta p • M p) (tsupport beta)ᶜ := by
    apply (contDiffOn_const (c := (0 : R3 →L[ℝ] R3))).congr
    intro p hp
    have hZero : beta p = 0 := image_eq_zero_of_notMem_tsupport hp
    simp only [hZero,hZeroMap]
  have hUnion : O ∪ (tsupport beta)ᶜ = univ := by
    apply eq_univ_iff_forall.mpr
    intro p
    by_cases hp : p ∈ tsupport beta
    · exact Or.inl (hTS hp)
    · exact Or.inr hp
  have hFirstSmooth : ContDiff ℝ ∞ (fun p => beta p • M p) :=
    contDiff_of_contDiffOn_union_of_isOpen hFirstLocal hFirstZero hUnion
      hO (isClosed_tsupport beta).isOpen_compl
  let Mext : P × R3 → R3 →L[ℝ] R3 := fun p =>
    beta p • M p+(1-beta p) • ContinuousLinearMap.id ℝ R3
  have hId : ContDiff ℝ ∞ (fun _ : P × R3 => ContinuousLinearMap.id ℝ R3) := contDiff_const
  have hMext : ContDiff ℝ ∞ Mext :=
    hFirstSmooth.add ((contDiff_const.sub hBetaSmooth).smul hId)
  have hWhere (p : P × R3) (hp : beta p ≠ 0) : p ∈ O := by
    apply hTS
    exact subset_tsupport beta hp
  have hSymext (p : P × R3) (X Y : R3) :
      inner ℝ (Mext p X) Y = inner ℝ (Mext p Y) X := by
    by_cases hp : beta p = 0
    · simp only [Mext,hp,hZeroMap,sub_zero,one_smul,zero_add,ContinuousLinearMap.id_apply]
      exact real_inner_comm Y X
    · simp only [Mext,ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.id_apply,inner_add_left,real_inner_smul_left]
      rw [hSym p (hWhere p hp) X Y,real_inner_comm X Y]
  have hPosext (p : P × R3) (X : R3) (hX : X ≠ 0) :
      0 < inner ℝ (Mext p X) X := by
    by_cases hp : beta p = 0
    · simpa only [Mext,hp,hZeroMap,sub_zero,one_smul,zero_add,
        ContinuousLinearMap.id_apply] using (real_inner_self_pos.mpr hX)
    · have hBetaPos : 0 < beta p := lt_of_le_of_ne (hBetaRange p).1 (Ne.symm hp)
      simp only [Mext,ContinuousLinearMap.add_apply,ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.id_apply,inner_add_left,real_inner_smul_left]
      exact add_pos_of_pos_of_nonneg
        (mul_pos hBetaPos (hPos p (hWhere p hp) X hX))
        (mul_nonneg (sub_nonneg.mpr (hBetaRange p).2) real_inner_self_nonneg)
  have hUnit (p : P × R3) : IsUnit (Mext p) :=
    isUnit_of_strictly_positive (Mext p) (hPosext p)
  let Qext : P × R3 → R3 →L[ℝ] R3 := fun p => Ring.inverse (Mext p)
  have hQext : ContDiff ℝ ∞ Qext := contDiff_actual_operatorRingInverse Mext hMext hUnit
  have hBoth (p : P × R3) (X : R3) : Mext p (Qext p X) = X ∧ Qext p (Mext p X) = X := by
    constructor
    · exact congrArg (fun A : R3 →L[ℝ] R3 => A X)
        (Ring.mul_inverse_cancel (Mext p) (hUnit p))
    · exact congrArg (fun A : R3 →L[ℝ] R3 => A X)
        (Ring.inverse_mul_cancel (Mext p) (hUnit p))
  have hEq (p : P × R3) (hp : p ∈ U) : Mext p = M p := by
    simp only [Mext,hBetaOne p hp,one_smul,sub_self,hZeroMap,add_zero]
  have hGerm (p : P × R3) (hp : p ∈ U) : Mext =ᶠ[𝓝 p] M := by
    filter_upwards [hUOpen.mem_nhds hp] with q hq
    exact hEq q hq
  refine ⟨Mext,hMext,hQext,hSymext,hPosext,hUnit,hBoth,U,hUOpen,hKU,hUO,hGerm,?_⟩
  intro p hp
  filter_upwards [hGerm p hp] with q hq
  exact congrArg (fun A : R3 →L[ℝ] R3 => Ring.inverse A) hq

#print axioms OAI.AnisotropicCalderon.ConnectionError.exists_contDiff_positive_operator_extension
end OAI.AnisotropicCalderon.ConnectionError
