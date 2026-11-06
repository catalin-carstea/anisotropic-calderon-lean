import Calderon.StrictWeightMomentCone
import Mathlib.Data.Matrix.Block
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Product moment compactness, full covariance, and rank-one minimization. -/
set_option autoImplicit false
noncomputable section
open Set Metric Matrix Filter Topology
open scoped Matrix.Norms.Elementwise
namespace OAI.AnisotropicCalderon.ProductHessianSeparation

local notation "V3" => (Fin 3 → ℝ)
local notation "I6" => (Fin 3 ⊕ Fin 3)
local notation "V6" => (I6 → ℝ)
local notation "M3" => Matrix (Fin 3) (Fin 3) ℝ
local notation "M6" => Matrix I6 I6 ℝ
local notation "SA3" => selfAdjoint M3
local notation "SA6" => selfAdjoint M6

def productMetricMomentSection (G1 G2 : M3) (ell1 ell2 a1 a2 : V3) : Set SA6 :=
  {D | (D : M6).PosSemidef ∧
    metricMomentCondition G1 ell1 a1 (D : M6).toBlocks₁₁ ∧
    metricMomentCondition G2 ell2 a2 (D : M6).toBlocks₂₂ ∧
    Matrix.trace (D : M6) = 1}

def tangentMetricMomentSection (G1 G2 : M3) (ell1 ell2 a1 a2 : V3) : Set SA6 :=
  {T | (T : M6).PosSemidef ∧
    (T : M6) *ᵥ Sum.elim ell1 (0 : V3) = 0 ∧
    (T : M6) *ᵥ Sum.elim (0 : V3) ell2 = 0 ∧
    Matrix.trace (G1 * (T : M6).toBlocks₁₁) = dotProduct a1 (G1 *ᵥ a1) ∧
    Matrix.trace (G2 * (T : M6).toBlocks₂₂) = dotProduct a2 (G2 *ᵥ a2)}

theorem isCompact_productMetricMomentSection
    (G1 G2 : M3) (hG1 : G1.PosDef) (hG2 : G2.PosDef)
    (ell1 ell2 a1 a2 : V3)
    (ha1 : dotProduct ell1 a1 = 1) (ha2 : dotProduct ell2 a2 = 1) :
    IsCompact (productMetricMomentSection G1 G2 ell1 ell2 a1 a2) := by
  classical
  let C : Set SA6 := productMetricMomentSection G1 G2 ell1 ell2 a1 a2
  let b1 : SA6 → SA3 := fun D =>
    ⟨(D : M6).toBlocks₁₁, (show (D : M6).IsHermitian from D.2).submatrix Sum.inl⟩
  let b2 : SA6 → SA3 := fun D =>
    ⟨(D : M6).toBlocks₂₂, (show (D : M6).IsHermitian from D.2).submatrix Sum.inr⟩
  have hb1 : Continuous b1 := by
    apply Continuous.subtype_mk
    apply continuous_matrix
    intro i j
    change Continuous (fun D : SA6 => (D : M6) (Sum.inl i) (Sum.inl j))
    exact Continuous.comp (f := fun D : SA6 => (D : M6))
      (g := fun B : M6 => B (Sum.inl i) (Sum.inl j))
      (continuous_apply_apply (Sum.inl i) (Sum.inl j)) continuous_subtype_val
  have hb2 : Continuous b2 := by
    apply Continuous.subtype_mk
    apply continuous_matrix
    intro i j
    change Continuous (fun D : SA6 => (D : M6) (Sum.inr i) (Sum.inr j))
    exact Continuous.comp (f := fun D : SA6 => (D : M6))
      (g := fun B : M6 => B (Sum.inr i) (Sum.inr j))
      (continuous_apply_apply (Sum.inr i) (Sum.inr j)) continuous_subtype_val
  have hPSDClosed : IsClosed {D : M6 | D.PosSemidef} := by
    have hSet : {D : M6 | D.PosSemidef} =
        {D : M6 | D.IsHermitian} ∩ ⋂ v : V6, {D : M6 | 0 ≤ dotProduct v (D *ᵥ v)} := by
      ext D
      simp only [mem_setOf_eq,mem_inter_iff,mem_iInter,
        Matrix.posSemidef_iff_dotProduct_mulVec,star_trivial]
    rw [hSet]
    apply IsClosed.inter
    · exact isClosed_eq (by fun_prop) continuous_id
    · apply isClosed_iInter
      intro v
      apply isClosed_le continuous_const
      simp only [dotProduct,Matrix.mulVec,Fintype.sum_sum_type,Fin.sum_univ_three]
      fun_prop
  have hMom1 := (metricMomentCondition_closed_convex_dual G1 hG1 ell1 a1 ha1).1
  have hMom2 := (metricMomentCondition_closed_convex_dual G2 hG2 ell2 a2 ha2).1
  have hCClosed : IsClosed C := by
    change IsClosed ({D : SA6 | (D : M6).PosSemidef} ∩
      ((b1 ⁻¹' {B : SA3 | metricMomentCondition G1 ell1 a1 (B : M3)}) ∩
      ((b2 ⁻¹' {B : SA3 | metricMomentCondition G2 ell2 a2 (B : M3)}) ∩
      {D : SA6 | Matrix.trace (D : M6) = 1})))
    exact (hPSDClosed.preimage continuous_subtype_val).inter ((hMom1.preimage hb1).inter
      ((hMom2.preimage hb2).inter (isClosed_eq (by fun_prop) continuous_const)))
  have hSAClosed : IsClosed {D : M6 | IsSelfAdjoint D} :=
    isClosed_eq (by fun_prop) continuous_id
  have hImageClosed : IsClosed ((fun D : SA6 => (D : M6)) '' C) :=
    (Topology.IsClosedEmbedding.subtypeVal hSAClosed).isClosedMap C hCClosed
  have hCube : IsCompact {D : M6 | ∀ r s, D r s ∈ Icc (-1 : ℝ) 1} := by
    exact (isCompact_Icc (a := (-1 : ℝ)) (b := 1)).matrix
  apply Subtype.isCompact_iff.mpr
  apply hCube.of_isClosed_subset hImageClosed
  rintro D ⟨Ds,hDs,rfl⟩ r s
  have hD : (Ds : M6).PosSemidef := hDs.1
  have htr : Matrix.trace (Ds : M6) = 1 := hDs.2.2.2
  have hDiag (k : I6) : 0 ≤ (Ds : M6) k k ∧ (Ds : M6) k k ≤ 1 := by
    refine ⟨hD.diag_nonneg,?_⟩
    have h := Finset.single_le_sum (fun i (_ : i ∈ Finset.univ) =>
      hD.diag_nonneg (i := i)) (Finset.mem_univ k)
    change (Ds : M6) k k ≤ Matrix.trace (Ds : M6) at h
    rwa [htr] at h
  have hSymm : (Ds : M6) s r = (Ds : M6) r s := by
    simpa only [star_trivial] using hD.isHermitian.apply r s
  have hPlus : 0 ≤ (Ds : M6) r r + (Ds : M6) s s + 2*(Ds : M6) r s := by
    have h := hD.dotProduct_mulVec_nonneg (Pi.single r 1 + Pi.single s 1)
    simp [dotProduct,Matrix.mulVec,Pi.single_apply,Finset.sum_add_distrib,
      Finset.mul_sum,Finset.sum_mul,add_mul,mul_add,hSymm] at h
    linarith only [h]
  have hMinus : 0 ≤ (Ds : M6) r r + (Ds : M6) s s - 2*(Ds : M6) r s := by
    have h := hD.dotProduct_mulVec_nonneg (Pi.single r 1 - Pi.single s 1)
    simp [dotProduct,Matrix.mulVec,Pi.single_apply,Finset.sum_sub_distrib,
      Finset.mul_sum,Finset.sum_mul,sub_mul,mul_sub,hSymm] at h
    linarith only [h]
  constructor <;> linarith only [hPlus,hMinus,(hDiag r).2,(hDiag s).2]

theorem exists_pos_normal_tangent_decomposition
    (G1 G2 : M3) (hG1 : G1.PosDef) (hG2 : G2.PosDef)
    (ell1 ell2 a1 a2 : V3)
    (ha1 : dotProduct ell1 a1 = 1) (ha2 : dotProduct ell2 a2 = 1)
    (D : M6) (hD : D.PosSemidef) (hne : D ≠ 0)
    (hm1 : metricMomentCondition G1 ell1 a1 D.toBlocks₁₁)
    (hm2 : metricMomentCondition G2 ell2 a2 D.toBlocks₂₂)
    (hker : D *ᵥ Sum.elim ell1 ell2 = 0) :
    let P : M6 := Matrix.fromBlocks
      (1 - Matrix.vecMulVec a1 ell1) 0 0 (1 - Matrix.vecMulVec a2 ell2)
    let Q : M6 := 1 - P
    let T : M6 := P * D * P.transpose
    let n : V6 := Sum.elim a1 (-a2)
    ∃ d : ℝ, 0 < d ∧
      dotProduct ell1 (D.toBlocks₁₁ *ᵥ ell1) = d ∧
      dotProduct ell2 (D.toBlocks₂₂ *ᵥ ell2) = d ∧
      D.toBlocks₁₁ *ᵥ ell1 = d • a1 ∧
      D.toBlocks₂₂ *ᵥ ell2 = d • a2 ∧
      D.toBlocks₁₂ *ᵥ ell2 = -d • a1 ∧
      D.toBlocks₂₁ *ᵥ ell1 = -d • a2 ∧
      Q * D * P.transpose = 0 ∧ P * D * Q.transpose = 0 ∧
      D = d • Matrix.vecMulVec n n + T ∧ T.PosSemidef ∧
      T *ᵥ Sum.elim ell1 (0 : V3) = 0 ∧
      T *ᵥ Sum.elim (0 : V3) ell2 = 0 ∧
      Matrix.trace (G1 * T.toBlocks₁₁) = d * dotProduct a1 (G1 *ᵥ a1) ∧
      Matrix.trace (G2 * T.toBlocks₂₂) = d * dotProduct a2 (G2 *ᵥ a2) := by
  classical
  let P : M6 := Matrix.fromBlocks
    (1 - Matrix.vecMulVec a1 ell1) 0 0 (1 - Matrix.vecMulVec a2 ell2)
  let Q : M6 := 1-P
  let T : M6 := P*D*P.transpose
  let n : V6 := Sum.elim a1 (-a2)
  let u1 : V6 := Sum.elim ell1 (0 : V3)
  let u2 : V6 := Sum.elim (0 : V3) ell2
  let A1 : V6 := Sum.elim a1 (0 : V3)
  let A2 : V6 := Sum.elim (0 : V3) a2
  let d1 : ℝ := dotProduct ell1 (D.toBlocks₁₁ *ᵥ ell1)
  let d2 : ℝ := dotProduct ell2 (D.toBlocks₂₂ *ᵥ ell2)
  have hRankApply (v w z : V3) :
      Matrix.vecMulVec v w *ᵥ z = dotProduct w z • v := by
    ext i
    simp only [Matrix.mulVec,dotProduct,Matrix.vecMulVec_apply,Pi.smul_apply,smul_eq_mul]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hRankApply6 (v w z : V6) :
      Matrix.vecMulVec v w *ᵥ z = dotProduct w z • v := by
    ext i
    simp only [Matrix.mulVec,dotProduct,Matrix.vecMulVec_apply,Pi.smul_apply,smul_eq_mul]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hdiag1 : D.toBlocks₁₁ *ᵥ ell1 = d1 • a1 := by
    have hk := hm1.2.2.2.1
    change (D.toBlocks₁₁-d1 • Matrix.vecMulVec a1 a1) *ᵥ ell1 = 0 at hk
    rw [Matrix.sub_mulVec,Matrix.smul_mulVec,hRankApply,
      dotProduct_comm a1 ell1,ha1,one_smul] at hk
    exact sub_eq_zero.mp hk
  have hdiag2 : D.toBlocks₂₂ *ᵥ ell2 = d2 • a2 := by
    have hk := hm2.2.2.2.1
    change (D.toBlocks₂₂-d2 • Matrix.vecMulVec a2 a2) *ᵥ ell2 = 0 at hk
    rw [Matrix.sub_mulVec,Matrix.smul_mulVec,hRankApply,
      dotProduct_comm a2 ell2,ha2,one_smul] at hk
    exact sub_eq_zero.mp hk
  have hker1 : D.toBlocks₁₁ *ᵥ ell1 + D.toBlocks₁₂ *ᵥ ell2 = 0 := by
    ext i
    have h := congrFun hker (Sum.inl i)
    simpa only [Matrix.mulVec,dotProduct,Fintype.sum_sum_type,Matrix.toBlocks₁₁,
      Matrix.toBlocks₁₂,Matrix.of_apply,Sum.elim_inl,Sum.elim_inr,Pi.add_apply,Pi.zero_apply] using h
  have hker2 : D.toBlocks₂₁ *ᵥ ell1 + D.toBlocks₂₂ *ᵥ ell2 = 0 := by
    ext i
    have h := congrFun hker (Sum.inr i)
    simpa only [Matrix.mulVec,dotProduct,Fintype.sum_sum_type,Matrix.toBlocks₂₁,
      Matrix.toBlocks₂₂,Matrix.of_apply,Sum.elim_inl,Sum.elim_inr,Pi.add_apply,Pi.zero_apply] using h
  have hcross1 : D.toBlocks₁₂ *ᵥ ell2 = -d1 • a1 := by
    rw [hdiag1] at hker1
    calc
      D.toBlocks₁₂ *ᵥ ell2 = (d1 • a1 + D.toBlocks₁₂ *ᵥ ell2)-d1 • a1 := by abel
      _ = -d1 • a1 := by rw [hker1]; simp
  have hcross2 : D.toBlocks₂₁ *ᵥ ell1 = -d2 • a2 := by
    rw [hdiag2] at hker2
    calc
      D.toBlocks₂₁ *ᵥ ell1 = (D.toBlocks₂₁ *ᵥ ell1+d2 • a2)-d2 • a2 := by abel
      _ = -d2 • a2 := by rw [hker2]; simp
  have hPair : dotProduct ell1 (D.toBlocks₁₂ *ᵥ ell2) =
      dotProduct ell2 (D.toBlocks₂₁ *ᵥ ell1) := by
    have h := hD.isHermitian.star_dotProduct_mulVec_comm u1 u2
    simpa [u1,u2,dotProduct,Matrix.mulVec,Fintype.sum_sum_type,
      Matrix.toBlocks₁₂,Matrix.toBlocks₂₁,Matrix.of_apply] using h
  have hdEq : d1 = d2 := by
    rw [hcross1,hcross2,dotProduct_smul,dotProduct_smul,ha1,ha2] at hPair
    simpa only [smul_eq_mul,mul_one,neg_inj] using hPair
  have hdNonneg : 0 ≤ d1 := hm1.2.1
  have hdPos : 0 < d1 := by
    by_contra hp
    have hz : d1 = 0 := le_antisymm (le_of_not_gt hp) hdNonneg
    have hzero (G : M3) (hG : G.PosDef) (ell a : V3)
        (ha : dotProduct ell a = 1) (B : M3)
        (hm : metricMomentCondition G ell a B)
        (hd : dotProduct ell (B *ᵥ ell) = 0) : B = 0 := by
      obtain ⟨w,v,hw,hv,hs,hB⟩ :=
        (metricMomentCondition_iff_sum_generators G hG ell a ha B).mp hm
      have hwzero (j : Fin 3) : w j = 0 := by
        have h := Finset.single_le_sum (fun k (_ : k ∈ Finset.univ) => hw k)
          (Finset.mem_univ j)
        rw [hs,hd] at h
        exact le_antisymm h (hw j)
      simp only [hB,hwzero,zero_smul,Finset.sum_const_zero]
    have h11 : D.toBlocks₁₁ = 0 := hzero G1 hG1 ell1 a1 ha1 _ hm1 hz
    have hz2 : d2 = 0 := hdEq.symm.trans hz
    have h22 : D.toBlocks₂₂ = 0 := hzero G2 hG2 ell2 a2 ha2 _ hm2 hz2
    have htrace : Matrix.trace D = 0 := by
      simp only [Matrix.trace,Fintype.sum_sum_type,Matrix.diag_apply]
      have h11' (i : Fin 3) : D (Sum.inl i) (Sum.inl i) = 0 := congrFun (congrFun h11 i) i
      have h22' (i : Fin 3) : D (Sum.inr i) (Sum.inr i) = 0 := congrFun (congrFun h22 i) i
      simp only [h11',h22',Finset.sum_const_zero,add_zero]
    exact hne (hD.trace_eq_zero_iff.mp htrace)
  have hDu1 : D *ᵥ u1 = d1 • n := by
    ext (i|i)
    · simpa [u1,n,Matrix.mulVec,dotProduct,Fintype.sum_sum_type,
        Matrix.toBlocks₁₁,Matrix.toBlocks₁₂,Matrix.toBlocks₂₁,Matrix.toBlocks₂₂,
        Matrix.of_apply] using congrFun hdiag1 i
    · simpa [u1,n,Matrix.mulVec,dotProduct,Fintype.sum_sum_type,← hdEq,
        Matrix.toBlocks₁₁,Matrix.toBlocks₁₂,Matrix.toBlocks₂₁,Matrix.toBlocks₂₂,
        Matrix.of_apply] using congrFun hcross2 i
  have hDu2 : D *ᵥ u2 = -d1 • n := by
    ext (i|i)
    · simpa [u2,n,Matrix.mulVec,dotProduct,Fintype.sum_sum_type,
        Matrix.toBlocks₁₁,Matrix.toBlocks₁₂,Matrix.toBlocks₂₁,Matrix.toBlocks₂₂,
        Matrix.of_apply] using congrFun hcross1 i
    · simpa [u2,n,Matrix.mulVec,dotProduct,Fintype.sum_sum_type,← hdEq,
        Matrix.toBlocks₁₁,Matrix.toBlocks₁₂,Matrix.toBlocks₂₁,Matrix.toBlocks₂₂,
        Matrix.of_apply] using congrFun hdiag2 i
  have hQRank : Q = Matrix.vecMulVec A1 u1 + Matrix.vecMulVec A2 u2 := by
    ext (i|i) (j|j) <;>
      simp [P,Q,A1,A2,u1,u2,Matrix.fromBlocks,Matrix.one_apply,Matrix.vecMulVec_apply]
  have hPn : P *ᵥ n = 0 := by
    ext (i|i) <;>
      simp [P,n,Matrix.fromBlocks_mulVec,Matrix.sub_mulVec,hRankApply,
        ha1,ha2]
  have hQn : Q *ᵥ n = n := by
    simp only [Q,Matrix.sub_mulVec,Matrix.one_mulVec,hPn,sub_zero]
  have hRows (v : V6) : v ᵥ* D = D *ᵥ v := by
    ext i
    simp only [Matrix.vecMul,Matrix.mulVec,dotProduct]
    apply Finset.sum_congr rfl
    intro j _
    have hsym : D j i = D i j := by
      simpa only [star_trivial] using hD.isHermitian.apply i j
    rw [hsym,mul_comm]
  have hQD : Q*D = d1 • Matrix.vecMulVec n n := by
    rw [hQRank,Matrix.add_mul,Matrix.vecMulVec_mul,Matrix.vecMulVec_mul,hRows,hRows,hDu1,hDu2]
    ext (i|i) (j|j) <;>
      simp only [Matrix.add_apply,Matrix.smul_apply,Matrix.vecMulVec_apply,A1,A2,n,
        Sum.elim_inl,Sum.elim_inr,Pi.zero_apply,Pi.neg_apply,Pi.smul_apply,smul_eq_mul] <;> ring
  have hDQ : D*Q.transpose = d1 • Matrix.vecMulVec n n := by
    calc
      D*Q.transpose = (Q*D).transpose := by
        rw [Matrix.transpose_mul,hD.isHermitian.isSymm.eq]
      _ = d1 • Matrix.vecMulVec n n := by
        rw [hQD]
        ext i j
        simp only [Matrix.transpose_apply,Matrix.smul_apply,Matrix.vecMulVec_apply,smul_eq_mul]
        ring
  have hRankTranspose (v w : V6) (B : M6) :
      Matrix.vecMulVec v w * B.transpose = Matrix.vecMulVec v (B *ᵥ w) := by
    ext i j
    simp only [Matrix.mul_apply,Matrix.transpose_apply,Matrix.vecMulVec_apply,
      Matrix.mulVec,dotProduct,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  have hMixed1 : Q*D*P.transpose = 0 := by
    rw [hQD,Matrix.smul_mul,hRankTranspose,hPn]
    simp only [Matrix.vecMulVec_zero,smul_zero]
  have hMixed2 : P*D*Q.transpose = 0 := by
    rw [Matrix.mul_assoc,hDQ,Matrix.mul_smul,Matrix.mul_vecMulVec,hPn]
    simp only [Matrix.zero_vecMulVec,smul_zero]
  have hQQ : Q*D*Q.transpose = d1 • Matrix.vecMulVec n n := by
    rw [hQD,Matrix.smul_mul,hRankTranspose,hQn]
  have hDecomp : D = d1 • Matrix.vecMulVec n n+T := by
    have hPQ : P+Q = 1 := by dsimp only [Q]; abel
    calc
      D = (P+Q)*D*(P.transpose+Q.transpose) := by
        rw [← Matrix.transpose_add,hPQ,Matrix.transpose_one,Matrix.one_mul,Matrix.mul_one]
      _ = T + P*D*Q.transpose + Q*D*P.transpose + Q*D*Q.transpose := by
        dsimp only [T]
        simp only [Matrix.add_mul,Matrix.mul_add]
        abel
      _ = d1 • Matrix.vecMulVec n n+T := by rw [hMixed1,hMixed2,hQQ]; abel
  have hTpsd : T.PosSemidef := by
    simpa only [T,Matrix.conjTranspose_eq_transpose_of_trivial] using
      hD.mul_mul_conjTranspose_same P
  have hPTranspose : P.transpose = Matrix.fromBlocks
      (1-Matrix.vecMulVec ell1 a1) 0 0 (1-Matrix.vecMulVec ell2 a2) := by
    ext (i|i) (j|j) <;>
      simp [P,Matrix.transpose_apply,Matrix.one_apply,Matrix.vecMulVec_apply,eq_comm] <;> ring
  have hPT1 : P.transpose *ᵥ u1 = 0 := by
    rw [hPTranspose]
    ext (i|i) <;>
      simp [u1,Matrix.fromBlocks_mulVec,Matrix.sub_mulVec,hRankApply,
        dotProduct_comm a1 ell1,ha1]
  have hPT2 : P.transpose *ᵥ u2 = 0 := by
    rw [hPTranspose]
    ext (i|i) <;>
      simp [u2,Matrix.fromBlocks_mulVec,Matrix.sub_mulVec,hRankApply,
        dotProduct_comm a2 ell2,ha2]
  have hTk1 : T *ᵥ u1 = 0 := by
    simp only [T,← Matrix.mulVec_mulVec,hPT1,Matrix.mulVec_zero]
  have hTk2 : T *ᵥ u2 = 0 := by
    simp only [T,← Matrix.mulVec_mulVec,hPT2,Matrix.mulVec_zero]
  have hT11 : T.toBlocks₁₁ = D.toBlocks₁₁-d1 • Matrix.vecMulVec a1 a1 := by
    ext i j
    have h := congrArg (fun B : M6 => B (Sum.inl i) (Sum.inl j)) hDecomp
    simp only [Matrix.add_apply,Matrix.smul_apply,Matrix.vecMulVec_apply,n,Sum.elim_inl,
      smul_eq_mul] at h
    change T (Sum.inl i) (Sum.inl j) = D (Sum.inl i) (Sum.inl j)-d1*(a1 i*a1 j)
    linarith only [h]
  have hT22 : T.toBlocks₂₂ = D.toBlocks₂₂-d1 • Matrix.vecMulVec a2 a2 := by
    ext i j
    have h := congrArg (fun B : M6 => B (Sum.inr i) (Sum.inr j)) hDecomp
    simp only [Matrix.add_apply,Matrix.smul_apply,Matrix.vecMulVec_apply,n,Sum.elim_inr,
      Pi.neg_apply,smul_eq_mul,neg_mul_neg] at h
    change T (Sum.inr i) (Sum.inr j) = D (Sum.inr i) (Sum.inr j)-d1*(a2 i*a2 j)
    linarith only [h]
  refine ⟨d1,hdPos,rfl,hdEq.symm,hdiag1,?_,hcross1,?_,hMixed1,hMixed2,hDecomp,
    hTpsd,hTk1,hTk2,?_,?_⟩
  · simpa only [hdEq] using hdiag2
  · simpa only [hdEq] using hcross2
  · rw [hT11]
    exact hm1.2.2.2.2
  · rw [hT22,hdEq]
    exact hm2.2.2.2.2

theorem exists_rankOne_minimizer_tangentMetricMomentSection
    (G1 G2 : M3) (hG1 : G1.PosDef) (hG2 : G2.PosDef)
    (ell1 ell2 a1 a2 : V3)
    (ha1 : dotProduct ell1 a1 = 1) (ha2 : dotProduct ell2 a2 = 1)
    (H : SA6) :
    ∃ v1 ∈ metricTangentSphere G1 ell1 a1,
      ∃ v2 ∈ metricTangentSphere G2 ell2 a2,
      let v : V6 := Sum.elim v1 v2
      ∃ T : SA6, (T : M6) = Matrix.vecMulVec v v ∧
        T ∈ tangentMetricMomentSection G1 G2 ell1 ell2 a1 a2 ∧
        (∀ S ∈ tangentMetricMomentSection G1 G2 ell1 ell2 a1 a2,
          Matrix.trace ((H : M6) * (T : M6)) ≤ Matrix.trace ((H : M6) * (S : M6))) := by
  classical
  letI : ContinuousSMul ℝ SA6 :=
    Topology.IsInducing.continuousSMul
      (M := ℝ) (X := M6) (Y := SA6)
      (g := fun T : SA6 => (T : M6)) (f := fun t : ℝ => t)
      Topology.IsInducing.subtypeVal continuous_id (fun {_ _} => rfl)
  letI : LocallyConvexSpace ℝ M6 :=
    inferInstanceAs (LocallyConvexSpace ℝ (I6 → I6 → ℝ))
  let coeL : SA6 →ₗ[ℝ] M6 :=
    { toFun := fun T : SA6 => (T : M6)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  letI : LocallyConvexSpace ℝ SA6 :=
    Topology.IsInducing.locallyConvexSpace (f := coeL)
      Topology.IsInducing.subtypeVal
  let C : Set SA6 := tangentMetricMomentSection G1 G2 ell1 ell2 a1 a2
  let A1 : ℝ := dotProduct a1 (G1 *ᵥ a1)
  let A2 : ℝ := dotProduct a2 (G2 *ᵥ a2)
  let e1 : V6 := Sum.elim ell1 (0 : V3)
  let e2 : V6 := Sum.elim (0 : V3) ell2
  have hApos (G : M3) (hG : G.PosDef) (ell a : V3)
      (ha : dotProduct ell a = 1) : 0 < dotProduct a (G *ᵥ a) := by
    have hane : a ≠ 0 := by
      intro h
      simp only [h,dotProduct_zero] at ha
      norm_num at ha
    simpa only [star_trivial] using hG.dotProduct_mulVec_pos hane
  have hA1 : 0 < A1 := hApos G1 hG1 ell1 a1 ha1
  have hA2 : 0 < A2 := hApos G2 hG2 ell2 a2 ha2
  have hSphere (G : M3) (hG : G.PosDef) (ell a : V3)
      (ha : dotProduct ell a = 1) : (metricTangentSphere G ell a).Nonempty := by
    have hm : metricMomentCondition G ell a 0 := by
      simp [metricMomentCondition,Matrix.PosSemidef.zero]
    obtain ⟨w,v,hw,hv,hs,heq⟩ :=
      (metricMomentCondition_iff_sum_generators G hG ell a ha 0).mp hm
    exact ⟨v 0,hv 0⟩
  have hRank (v w z : V6) :
      Matrix.vecMulVec v w *ᵥ z = dotProduct w z • v := by
    ext i
    simp only [Matrix.mulVec,dotProduct,Matrix.vecMulVec_apply,Pi.smul_apply,smul_eq_mul]
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hRankTrace (G : M3) (v : V3) :
      Matrix.trace (G*Matrix.vecMulVec v v) = dotProduct v (G *ᵥ v) := by
    rw [Matrix.mul_vecMulVec,Matrix.trace_vecMulVec]
    exact dotProduct_comm _ _
  have hRankPSD (v : V6) : (Matrix.vecMulVec v v).PosSemidef := by
    simpa only [star_trivial] using Matrix.posSemidef_vecMulVec_self_star v
  have hNonempty : C.Nonempty := by
    obtain ⟨v1,hv1⟩ := hSphere G1 hG1 ell1 a1 ha1
    obtain ⟨v2,hv2⟩ := hSphere G2 hG2 ell2 a2 ha2
    let v : V6 := Sum.elim v1 v2
    let T : SA6 := ⟨Matrix.vecMulVec v v,(hRankPSD v).isHermitian⟩
    refine ⟨T,hRankPSD v,?_,?_,?_,?_⟩
    · change Matrix.vecMulVec v v *ᵥ e1 = 0
      rw [hRank]
      have hdot : dotProduct v e1 = 0 := by
        change dotProduct (Sum.elim v1 v2) (Sum.elim ell1 (0 : V3)) = 0
        rw [sumElim_dotProduct_sumElim,dotProduct_zero,add_zero,dotProduct_comm]
        exact hv1.1
      rw [hdot,zero_smul]
    · change Matrix.vecMulVec v v *ᵥ e2 = 0
      rw [hRank]
      have hdot : dotProduct v e2 = 0 := by
        change dotProduct (Sum.elim v1 v2) (Sum.elim (0 : V3) ell2) = 0
        rw [sumElim_dotProduct_sumElim,dotProduct_zero,zero_add,dotProduct_comm]
        exact hv2.1
      rw [hdot,zero_smul]
    · change Matrix.trace (G1*Matrix.vecMulVec v1 v1) = A1
      rw [hRankTrace]
      exact hv1.2
    · change Matrix.trace (G2*Matrix.vecMulVec v2 v2) = A2
      rw [hRankTrace]
      exact hv2.2
  have hPSDClosed : IsClosed {B : M6 | B.PosSemidef} := by
    have hSet : {B : M6 | B.PosSemidef} =
        {B : M6 | B.IsHermitian} ∩ ⋂ z : V6, {B : M6 | 0 ≤ dotProduct z (B *ᵥ z)} := by
      ext B
      simp only [mem_setOf_eq,mem_inter_iff,mem_iInter,
        Matrix.posSemidef_iff_dotProduct_mulVec,star_trivial]
    rw [hSet]
    refine (isClosed_eq (by fun_prop) continuous_id).inter (isClosed_iInter fun z => ?_)
    apply isClosed_le continuous_const
    simp only [dotProduct,Matrix.mulVec,Fintype.sum_sum_type,Fin.sum_univ_three]
    fun_prop
  have hEntry (i j : I6) : Continuous (fun T : SA6 => (T : M6) i j) :=
    (show Continuous (fun B : M6 => B i j) from continuous_apply_apply i j).comp
      (show Continuous (fun T : SA6 => (T : M6)) from continuous_subtype_val)
  have hTrace1 : Continuous (fun T : SA6 => Matrix.trace (G1*(T : M6).toBlocks₁₁)) := by
    have hSum : Continuous (fun T : SA6 => ∑ i : Fin 3, ∑ j : Fin 3,
        G1 i j*(T : M6) (Sum.inl j) (Sum.inl i)) :=
      continuous_finsetSum Finset.univ (fun i _ =>
        continuous_finsetSum Finset.univ (fun j _ =>
          continuous_const.mul (hEntry (Sum.inl j) (Sum.inl i))))
    simpa only [Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,
      Matrix.toBlocks₁₁,Matrix.of_apply] using hSum
  have hTrace2 : Continuous (fun T : SA6 => Matrix.trace (G2*(T : M6).toBlocks₂₂)) := by
    have hSum : Continuous (fun T : SA6 => ∑ i : Fin 3, ∑ j : Fin 3,
        G2 i j*(T : M6) (Sum.inr j) (Sum.inr i)) :=
      continuous_finsetSum Finset.univ (fun i _ =>
        continuous_finsetSum Finset.univ (fun j _ =>
          continuous_const.mul (hEntry (Sum.inr j) (Sum.inr i))))
    simpa only [Matrix.trace,Matrix.diag_apply,Matrix.mul_apply,
      Matrix.toBlocks₂₂,Matrix.of_apply] using hSum
  have hClosed : IsClosed C := by
    change IsClosed ({T : SA6 | (T : M6).PosSemidef} ∩
      ({T : SA6 | (T : M6) *ᵥ e1 = 0} ∩
      ({T : SA6 | (T : M6) *ᵥ e2 = 0} ∩
      ({T : SA6 | Matrix.trace (G1*(T : M6).toBlocks₁₁) = A1} ∩
      {T : SA6 | Matrix.trace (G2*(T : M6).toBlocks₂₂) = A2}))))
    refine (hPSDClosed.preimage continuous_subtype_val).inter
      ((isClosed_eq ?_ continuous_const).inter ((isClosed_eq ?_ continuous_const).inter
      ((isClosed_eq ?_ continuous_const).inter (isClosed_eq ?_ continuous_const))))
    · try simp only [Matrix.mulVec,dotProduct,Fintype.sum_sum_type,Fin.sum_univ_three]
      fun_prop
    · try simp only [Matrix.mulVec,dotProduct,Fintype.sum_sum_type,Fin.sum_univ_three]
      fun_prop
    · exact hTrace1
    · exact hTrace2
  have hWeightedBound (G : M3) (hG : G.PosDef) :
      ∃ beta : ℝ, 0 < beta ∧ ∀ B : M3, B.PosSemidef →
        beta*Matrix.trace B ≤ Matrix.trace (G*B) := by
    let lam : Fin 3 → ℝ := hG.isHermitian.eigenvalues
    let U : M3 := hG.isHermitian.eigenvectorUnitary
    let beta : ℝ := min (lam 0) (min (lam 1) (lam 2))
    have hLam (j : Fin 3) : 0 < lam j := hG.eigenvalues_pos j
    have hBeta : 0 < beta := lt_min (hLam 0) (lt_min (hLam 1) (hLam 2))
    have hLe (j : Fin 3) : beta ≤ lam j := by
      fin_cases j
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (min_le_left _ _)
      · exact (min_le_right _ _).trans (min_le_right _ _)
    refine ⟨beta,hBeta,fun B hB => ?_⟩
    let W : M3 := U.conjTranspose*B*U
    have hW : W.PosSemidef := hB.conjTranspose_mul_mul_same U
    have hUW : U*U.conjTranspose = 1 := by
      exact Unitary.coe_mul_star_self hG.isHermitian.eigenvectorUnitary
    have hTrW : Matrix.trace W = Matrix.trace B := by
      change Matrix.trace (U.conjTranspose*B*U) = Matrix.trace B
      rw [Matrix.trace_mul_cycle,hUW,Matrix.one_mul]
    have hGspec : G = U*Matrix.diagonal lam*U.conjTranspose := by
      simpa only [Unitary.conjStarAlgAut_apply,Matrix.star_eq_conjTranspose,RCLike.ofReal_real_eq_id,
        Function.comp_def,id_eq,U,lam] using hG.isHermitian.spectral_theorem
    have hTrace : Matrix.trace (G*B) = ∑ j, lam j * W j j := by
      calc
        Matrix.trace (G*B) = Matrix.trace ((U*Matrix.diagonal lam)*(U.conjTranspose*B)) := by
          rw [hGspec]
          simp only [Matrix.mul_assoc]
        _ = Matrix.trace ((U.conjTranspose*B)*U*Matrix.diagonal lam) :=
          Matrix.trace_mul_cycle _ _ _
        _ = Matrix.trace (Matrix.diagonal lam*W) := Matrix.trace_mul_comm _ _
        _ = ∑ j, lam j*W j j := by
          simp [Matrix.trace,Matrix.mul_apply,Matrix.diagonal,Fin.sum_univ_three]
    rw [hTrace,← hTrW,Matrix.trace,Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    exact mul_le_mul_of_nonneg_right (hLe j) hW.diag_nonneg
  obtain ⟨beta1,hBeta1,hBound1⟩ := hWeightedBound G1 hG1
  obtain ⟨beta2,hBeta2,hBound2⟩ := hWeightedBound G2 hG2
  let beta : ℝ := min beta1 beta2
  have hBeta : 0 < beta := lt_min hBeta1 hBeta2
  let R : ℝ := (A1+A2)/beta+1
  have hR : 0 < R := by positivity
  have hTraceBound (T : SA6) (hT : T ∈ C) : Matrix.trace (T : M6) ≤ R := by
    have hp : (T : M6).PosSemidef := hT.1
    have hp1 : Matrix.PosSemidef ((T : M6).toBlocks₁₁) := hp.submatrix Sum.inl
    have hp2 : Matrix.PosSemidef ((T : M6).toBlocks₂₂) := hp.submatrix Sum.inr
    have h1 := hBound1 _ hp1
    have h2 := hBound2 _ hp2
    rw [hT.2.2.2.1] at h1
    rw [hT.2.2.2.2] at h2
    have h1' := (mul_le_mul_of_nonneg_right (min_le_left beta1 beta2) hp1.trace_nonneg).trans h1
    have h2' := (mul_le_mul_of_nonneg_right (min_le_right beta1 beta2) hp2.trace_nonneg).trans h2
    have hSplit : Matrix.trace (T : M6) =
        Matrix.trace (T : M6).toBlocks₁₁+Matrix.trace (T : M6).toBlocks₂₂ := by
      simp only [Matrix.trace,Matrix.diag_apply,Fintype.sum_sum_type,
        Matrix.toBlocks₁₁,Matrix.toBlocks₂₂,Matrix.of_apply]
    have hsum : beta*Matrix.trace (T : M6) ≤ A1+A2 := by
      rw [hSplit,mul_add]
      exact add_le_add h1' h2'
    have hdiv : Matrix.trace (T : M6) ≤ (A1+A2)/beta :=
      (le_div_iff₀ hBeta).mpr (by simpa only [mul_comm] using hsum)
    exact hdiv.trans (by dsimp only [R]; linarith)
  have hCube : IsCompact {B : M6 | ∀ i j, B i j ∈ Icc (-R) R} := by
    exact (isCompact_Icc (a := -R) (b := R)).matrix
  have hSAClosed : IsClosed {B : M6 | IsSelfAdjoint B} :=
    isClosed_eq (by fun_prop) continuous_id
  have hImageClosed : IsClosed ((fun T : SA6 => (T : M6)) '' C) :=
    (Topology.IsClosedEmbedding.subtypeVal hSAClosed).isClosedMap C hClosed
  have hCompact : IsCompact C := by
    apply Subtype.isCompact_iff.mpr
    apply hCube.of_isClosed_subset hImageClosed
    rintro B ⟨T,hT,rfl⟩ i j
    have hp : (T : M6).PosSemidef := hT.1
    have hdiag (r : I6) : (T : M6) r r ≤ R := by
      have h := Finset.single_le_sum (fun k (_ : k ∈ Finset.univ) =>
        hp.diag_nonneg (i := k)) (Finset.mem_univ r)
      change (T : M6) r r ≤ Matrix.trace (T : M6) at h
      exact h.trans (hTraceBound T hT)
    have hSymm : (T : M6) j i = (T : M6) i j := by
      simpa only [star_trivial] using hp.isHermitian.apply i j
    have hPlus : 0 ≤ (T : M6) i i+(T : M6) j j+2*(T : M6) i j := by
      have h := hp.dotProduct_mulVec_nonneg (Pi.single i 1+Pi.single j 1)
      simp [dotProduct,Matrix.mulVec,Pi.single_apply,Finset.sum_add_distrib,
        Finset.mul_sum,Finset.sum_mul,add_mul,mul_add,hSymm] at h
      linarith only [h]
    have hMinus : 0 ≤ (T : M6) i i+(T : M6) j j-2*(T : M6) i j := by
      have h := hp.dotProduct_mulVec_nonneg (Pi.single i 1-Pi.single j 1)
      simp [dotProduct,Matrix.mulVec,Pi.single_apply,Finset.sum_sub_distrib,
        Finset.mul_sum,Finset.sum_mul,sub_mul,mul_sub,hSymm] at h
      linarith only [h]
    constructor <;> linarith only [hPlus,hMinus,hdiag i,hdiag j]
  letI : FiniteDimensional ℝ SA6 := FiniteDimensional.of_injective
    (selfAdjoint.submodule ℝ M6).subtype Subtype.coe_injective
  let fL : SA6 →ₗ[ℝ] ℝ :=
    { toFun := fun T => Matrix.trace ((H : M6)*(T : M6))
      map_add' := fun S T => by
        change Matrix.trace ((H : M6)*((S : M6)+(T : M6))) = _
        rw [Matrix.mul_add,Matrix.trace_add]
      map_smul' := fun s T => by
        change Matrix.trace ((H : M6)*(s • (T : M6))) = s • Matrix.trace ((H : M6)*(T : M6))
        rw [Matrix.mul_smul,Matrix.trace_smul] }
  let f : SA6 →L[ℝ] ℝ := fL.toContinuousLinearMap
  let F : Set SA6 := {T ∈ C | ∀ S ∈ C, f T ≤ f S}
  have hFnonempty : F.Nonempty := by
    obtain ⟨T,hT,hMin⟩ := hCompact.exists_isMinOn hNonempty f.continuous.continuousOn
    exact ⟨T,hT,hMin⟩
  have hExposed : IsExposed ℝ C F := by
    intro _
    refine ⟨-f,?_⟩
    ext T
    simp only [F,mem_setOf_eq,ContinuousLinearMap.neg_apply,neg_le_neg_iff]
  obtain ⟨T,hText⟩ := (hExposed.isCompact hCompact).extremePoints_nonempty hFnonempty
  have hT : T ∈ C := hText.1.1
  have hMin : ∀ S ∈ C, f T ≤ f S := hText.1.2
  have hExtreme : T ∈ C.extremePoints ℝ :=
    hExposed.isExtreme.extremePoints_subset_extremePoints hText
  have hp : (T : M6).PosSemidef := hT.1
  let lam : I6 → ℝ := hp.isHermitian.eigenvalues
  let u : I6 → V6 := fun j => (hp.isHermitian.eigenvectorBasis j : V6)
  have hLam (j : I6) : 0 ≤ lam j := hp.eigenvalues_nonneg j
  have hEig (j : I6) : (T : M6) *ᵥ u j = lam j • u j := hp.isHermitian.mulVec_eigenvectorBasis j
  have hOrtho (i j : I6) : dotProduct (u i) (u j) = if i=j then 1 else 0 := by
    have h : dotProduct (u j) (u i) = if i=j then 1 else 0 := by
      simpa only [u,EuclideanSpace.inner_eq_star_dotProduct,star_trivial] using
        hp.isHermitian.eigenvectorBasis.inner_eq_ite i j
    rwa [dotProduct_comm] at h
  have hSpecEntry (i j : I6) : (T : M6) i j = ∑ k, lam k*u k i*u k j := by
    have hs := hp.isHermitian.spectral_theorem
    rw [hs]
    simp only [Unitary.conjStarAlgAut_apply,Matrix.star_eq_conjTranspose,
      Matrix.mul_apply,Matrix.diagonal_apply,Matrix.of_apply,
      Matrix.conjTranspose_apply,star_trivial,Matrix.IsHermitian.eigenvectorUnitary_apply,
      RCLike.ofReal_real_eq_id,Function.comp_apply,id_eq,lam,u,
      Fintype.sum_sum_type,Fin.sum_univ_three]
    norm_num <;> ring
  have hSpec : (T : M6) = ∑ j, lam j • Matrix.vecMulVec (u j) (u j) := by
    ext i k
    simpa only [Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,
      Matrix.vecMulVec_apply,mul_assoc] using hSpecEntry i k
  have hSumMulVec (B : I6 → M6) (z : V6) : (∑ j, B j) *ᵥ z = ∑ j, B j *ᵥ z := by
    ext i
    simp only [Matrix.mulVec,dotProduct,Matrix.sum_apply,Finset.sum_apply,Finset.sum_mul]
    rw [Finset.sum_comm]
  have hRankQuad (v z : V6) : dotProduct z (Matrix.vecMulVec v v *ᵥ z) = (dotProduct v z)^2 := by
    rw [hRank,dotProduct_smul,smul_eq_mul,dotProduct_comm z v]
    ring
  have hQuad (z : V6) : dotProduct z ((T : M6) *ᵥ z) =
      ∑ j, lam j*(dotProduct (u j) z)^2 := by
    rw [hSpec,hSumMulVec]
    simp only [dotProduct_sum,Matrix.smul_mulVec,dotProduct_smul,smul_eq_mul,hRankQuad]
  have hKernel (i : I6) (hi : 0 < lam i) :
      dotProduct e1 (u i) = 0 ∧ dotProduct e2 (u i) = 0 := by
    have hk (e : V6) (he : (T : M6) *ᵥ e = 0) : dotProduct e (u i) = 0 := by
      have hc := hp.isHermitian.star_dotProduct_mulVec_comm e (u i)
      simp only [star_trivial,he,dotProduct_zero] at hc
      rw [hEig,dotProduct_smul,smul_eq_mul] at hc
      exact (mul_eq_zero.mp hc).resolve_left hi.ne'
    exact ⟨hk e1 hT.2.1,hk e2 hT.2.2.1⟩
  have hSome : ∃ j : I6, 0 < lam j := by
    by_contra hn
    push_neg at hn
    have hz (j : I6) : lam j = 0 := le_antisymm (hn j) (hLam j)
    have hTzero : (T : M6) = 0 := by simp only [hSpec,hz,zero_smul,Finset.sum_const_zero]
    have htrace := hT.2.2.2.1
    have hZero11 : (T : M6).toBlocks₁₁ = 0 := by
      rw [hTzero]
      ext i k
      rfl
    rw [hZero11,Matrix.mul_zero,Matrix.trace_zero] at htrace
    exact hA1.ne' htrace.symm
  have hUnique (j k : I6) (hj : 0 < lam j) (hk : 0 < lam k) : j = k := by
    by_contra hjk
    let v : V6 := u j
    let w : V6 := u k
    have hvv : dotProduct v v = 1 := by simpa only [v,if_pos rfl,ite_true] using hOrtho j j
    have hww : dotProduct w w = 1 := by simpa only [w,if_pos rfl,ite_true] using hOrtho k k
    have hvw : dotProduct v w = 0 := by simpa only [v,w,if_neg hjk] using hOrtho j k
    have hwv : dotProduct w v = 0 := by rw [dotProduct_comm]; exact hvw
    let EL : (Fin 3 → ℝ) →ₗ[ℝ] M6 :=
      { toFun := fun x => x 0 • Matrix.vecMulVec v v +
          x 1 • (Matrix.vecMulVec v w+Matrix.vecMulVec w v) +
          x 2 • Matrix.vecMulVec w w
        map_add' := fun x y => by
          simp only [Pi.add_apply,add_smul]
          abel
        map_smul' := fun s x => by
          simp only [Pi.smul_apply,RingHom.id_apply,smul_eq_mul,mul_smul,smul_add] }
    let CL : (Fin 3 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ) :=
      { toFun := fun x i => if i=0 then Matrix.trace (G1*(EL x).toBlocks₁₁)
          else Matrix.trace (G2*(EL x).toBlocks₂₂)
        map_add' := fun x y => by
          ext i
          by_cases hi : i=0
          · simp only [if_pos hi,Pi.add_apply]
            rw [map_add]
            change Matrix.trace (G1*((EL x).toBlocks₁₁+(EL y).toBlocks₁₁)) = _
            rw [Matrix.mul_add,Matrix.trace_add]
          · simp only [if_neg hi,Pi.add_apply]
            rw [map_add]
            change Matrix.trace (G2*((EL x).toBlocks₂₂+(EL y).toBlocks₂₂)) = _
            rw [Matrix.mul_add,Matrix.trace_add]
        map_smul' := fun s x => by
          ext i
          by_cases hi : i=0
          · simp only [if_pos hi,Pi.smul_apply,smul_eq_mul]
            rw [map_smul]
            change Matrix.trace (G1*(s • (EL x).toBlocks₁₁)) = s*Matrix.trace (G1*(EL x).toBlocks₁₁)
            rw [Matrix.mul_smul,Matrix.trace_smul]
            rfl
          · simp only [if_neg hi,Pi.smul_apply,smul_eq_mul]
            rw [map_smul]
            change Matrix.trace (G2*(s • (EL x).toBlocks₂₂)) = s*Matrix.trace (G2*(EL x).toBlocks₂₂)
            rw [Matrix.mul_smul,Matrix.trace_smul]
            rfl }
    have hNotInjective : ¬ Function.Injective CL := by
      intro hinj
      have hd := CL.finrank_le_finrank_of_injective hinj
      simp only [Module.finrank_fin_fun] at hd
      omega
    have hex : ∃ x y, CL x = CL y ∧ x ≠ y := by
      exact Function.not_injective_iff.mp hNotInjective
    obtain ⟨x,y,hxy,hne⟩ := hex
    let z : Fin 3 → ℝ := x-y
    have hz : z ≠ 0 := sub_ne_zero.mpr hne
    have hCz : CL z = 0 := by simp only [z,map_sub,hxy,sub_self]
    let E : M6 := EL z
    have hEu : dotProduct v (E *ᵥ v) = z 0 := by
      simp only [E,EL,LinearMap.coe_mk,AddHom.coe_mk,Matrix.add_mulVec,
        Matrix.smul_mulVec,hRank,dotProduct_add,dotProduct_smul,smul_eq_mul,
        hvv,hww,hvw,hwv,dotProduct_zero,mul_zero,mul_one,zero_smul,one_smul,add_zero,zero_add]
    have hEuv : dotProduct v (E *ᵥ w) = z 1 := by
      simp only [E,EL,LinearMap.coe_mk,AddHom.coe_mk,Matrix.add_mulVec,
        Matrix.smul_mulVec,hRank,dotProduct_add,dotProduct_smul,smul_eq_mul,
        hvv,hww,hvw,hwv,dotProduct_zero,mul_zero,mul_one,zero_smul,one_smul,add_zero,zero_add]
    have hEw : dotProduct w (E *ᵥ w) = z 2 := by
      simp only [E,EL,LinearMap.coe_mk,AddHom.coe_mk,Matrix.add_mulVec,
        Matrix.smul_mulVec,hRank,dotProduct_add,dotProduct_smul,smul_eq_mul,
        hvv,hww,hvw,hwv,dotProduct_zero,mul_zero,mul_one,zero_smul,one_smul,add_zero,zero_add]
    have hEne : E ≠ 0 := by
      intro he
      apply hz
      have h0 : z 0 = 0 := by simpa only [he,Matrix.zero_mulVec,dotProduct_zero] using hEu.symm
      have h1 : z 1 = 0 := by simpa only [he,Matrix.zero_mulVec,dotProduct_zero] using hEuv.symm
      have h2 : z 2 = 0 := by simpa only [he,Matrix.zero_mulVec,dotProduct_zero] using hEw.symm
      ext i
      fin_cases i <;> assumption
    have hEHerm : E.IsHermitian := by
      apply Matrix.IsHermitian.ext
      intro r s
      simp only [E,EL,LinearMap.coe_mk,AddHom.coe_mk,Matrix.add_apply,
        Matrix.smul_apply,Matrix.vecMulVec_apply,smul_eq_mul,star_trivial]
      ring
    have hEker (e : V6) (he1 : dotProduct e v = 0) (he2 : dotProduct e w = 0) : E *ᵥ e = 0 := by
      have he1' : dotProduct v e = 0 := by rw [dotProduct_comm]; exact he1
      have he2' : dotProduct w e = 0 := by rw [dotProduct_comm]; exact he2
      simp only [E,EL,LinearMap.coe_mk,AddHom.coe_mk,Matrix.add_mulVec,
        Matrix.smul_mulVec,hRank,he1',he2',zero_smul,add_zero,smul_zero]
    have hEker1 : E *ᵥ e1 = 0 := hEker e1 (hKernel j hj).1 (hKernel k hk).1
    have hEker2 : E *ᵥ e2 = 0 := hEker e2 (hKernel j hj).2 (hKernel k hk).2
    have hTrace1 : Matrix.trace (G1*E.toBlocks₁₁) = 0 := by
      simpa only [CL,E,LinearMap.coe_mk,AddHom.coe_mk,if_pos rfl,ite_true,Pi.zero_apply] using congrFun hCz 0
    have hTrace2 : Matrix.trace (G2*E.toBlocks₂₂) = 0 := by
      have hi : (1 : Fin 2) ≠ 0 := by decide
      simpa only [CL,E,LinearMap.coe_mk,AddHom.coe_mk,if_neg hi,Pi.zero_apply] using congrFun hCz 1
    let mu : ℝ := min (lam j) (lam k)
    let L : ℝ := |z 0|+|z 1|+|z 2|+1
    let t : ℝ := mu/(2*L)
    have hmu : 0 < mu := lt_min hj hk
    have hL : 0 < L := by dsimp only [L]; positivity
    have ht : 0 < t := div_pos hmu (mul_pos (by norm_num) hL)
    have htL : t*L = mu/2 := by
      dsimp only [t]
      field_simp [hL.ne']
    have hEQuad (q : V6) : dotProduct q (E *ᵥ q) =
        z 0*(dotProduct v q)^2 + 2*z 1*dotProduct v q*dotProduct w q +
          z 2*(dotProduct w q)^2 := by
      simp only [E,EL,LinearMap.coe_mk,AddHom.coe_mk,Matrix.add_mulVec,
        Matrix.smul_mulVec,hRank,dotProduct_add,dotProduct_smul,smul_eq_mul]
      simp only [dotProduct_comm q v,dotProduct_comm q w]
      ring
    have hEbound (q : V6) : |dotProduct q (E *ᵥ q)| ≤
        L*((dotProduct v q)^2+(dotProduct w q)^2) := by
      let a : ℝ := dotProduct v q
      let b : ℝ := dotProduct w q
      have hab : 2*|a*b| ≤ a^2+b^2 := by
        nlinarith only [sq_nonneg (|a|-|b|),sq_abs a,sq_abs b,abs_mul a b]
      have hzb := mul_le_mul_of_nonneg_left hab (abs_nonneg (z 1))
      have hTriangle : |z 0*a^2+2*z 1*a*b+z 2*b^2| ≤
          |z 0| *a^2+2*|z 1| *|a*b|+|z 2| *b^2 := by
        calc
          |z 0*a^2+2*z 1*a*b+z 2*b^2| ≤
              |z 0*a^2|+|2*z 1*a*b|+|z 2*b^2| := by
            have h1 : |z 0*a^2+2*z 1*a*b+z 2*b^2| ≤
                |z 0*a^2+2*z 1*a*b|+|z 2*b^2| := abs_add_le _ _
            have h2 : |z 0*a^2+2*z 1*a*b| ≤ |z 0*a^2|+|2*z 1*a*b| := abs_add_le _ _
            linarith only [h1,h2]
          _ = |z 0| *a^2+2*|z 1| *|a*b|+|z 2| *b^2 := by
            simp only [abs_mul,abs_two,abs_sq]
            ring
      rw [hEQuad]
      change |z 0*a^2+2*z 1*a*b+z 2*b^2| ≤ L*(a^2+b^2)
      dsimp only [L]
      nlinarith only [hTriangle,hzb,sq_nonneg a,sq_nonneg b,
        mul_nonneg (abs_nonneg (z 0)) (sq_nonneg b),
        mul_nonneg (abs_nonneg (z 2)) (sq_nonneg a)]
    have hTbound (q : V6) : mu*((dotProduct v q)^2+(dotProduct w q)^2) ≤
        dotProduct q ((T : M6) *ᵥ q) := by
      let g : I6 → ℝ := fun i => lam i*(dotProduct (u i) q)^2
      have hg (i : I6) : 0 ≤ g i := mul_nonneg (hLam i) (sq_nonneg _)
      have hPart : (∑ i : I6, ((if i=j then g j else 0)+(if i=k then g k else 0))) ≤ ∑ i, g i := by
        apply Finset.sum_le_sum
        intro i _
        by_cases hi : i=j
        · subst i
          simp only [if_pos rfl,if_neg hjk,ite_true,add_zero,le_refl]
        · by_cases hi' : i=k
          · subst i
            simp only [if_neg (Ne.symm hjk),if_pos rfl,ite_true,zero_add,le_refl]
          · simp only [if_neg hi,if_neg hi',zero_add]
            exact hg i
      have hTwo : g j+g k ≤ ∑ i, g i := by
        simpa only [Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,if_pos] using hPart
      have hjBound := mul_le_mul_of_nonneg_right (min_le_left (lam j) (lam k)) (sq_nonneg (dotProduct v q))
      have hkBound := mul_le_mul_of_nonneg_right (min_le_right (lam j) (lam k)) (sq_nonneg (dotProduct w q))
      rw [hQuad]
      change mu*((dotProduct v q)^2+(dotProduct w q)^2) ≤ ∑ i,g i
      dsimp only [g,v,w,mu] at hTwo hjBound hkBound ⊢
      nlinarith only [hTwo,hjBound,hkBound]
    have hPerturb (s : ℝ) (hs : |s| ≤ t) : ((T : M6)+s • E).PosSemidef := by
      apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
      · apply Matrix.IsHermitian.ext
        intro r q
        have hT' := hp.isHermitian.apply r q
        have hE' := hEHerm.apply r q
        simp only [star_trivial] at hT' hE' ⊢
        simp only [Matrix.add_apply,Matrix.smul_apply,smul_eq_mul]
        rw [hT',hE']
      · intro q
        have he := hEbound q
        have hbase := hTbound q
        have hscaled : |s*dotProduct q (E *ᵥ q)| ≤
            (mu/2)*((dotProduct v q)^2+(dotProduct w q)^2) := by
          rw [abs_mul]
          calc
            |s| *|dotProduct q (E *ᵥ q)| ≤
                t*(L*((dotProduct v q)^2+(dotProduct w q)^2)) :=
              mul_le_mul hs he (abs_nonneg _) ht.le
            _ = (mu/2)*((dotProduct v q)^2+(dotProduct w q)^2) := by
              rw [← mul_assoc,htL]
        have hlo := (abs_le.mp hscaled).1
        have hPosBase : 0 ≤ (mu/2)*((dotProduct v q)^2+(dotProduct w q)^2) :=
          mul_nonneg (div_nonneg hmu.le (by norm_num)) (add_nonneg (sq_nonneg _) (sq_nonneg _))
        have hq : 0 ≤ dotProduct q ((T : M6) *ᵥ q)+s*dotProduct q (E *ᵥ q) := by
          nlinarith only [hbase,hlo,hPosBase]
        simpa only [star_trivial,Matrix.add_mulVec,Matrix.smul_mulVec,
          dotProduct_add,dotProduct_smul,smul_eq_mul] using hq
    let Es : SA6 := ⟨E,hEHerm⟩
    have hEsne : Es ≠ 0 := by intro he; exact hEne (congrArg (fun X : SA6 => (X : M6)) he)
    have hTk1 : (T : M6) *ᵥ e1 = 0 := hT.2.1
    have hTk2 : (T : M6) *ᵥ e2 = 0 := hT.2.2.1
    have hMember (s : ℝ) (hs : |s| ≤ t) : T+s • Es ∈ C := by
      refine ⟨hPerturb s hs,?_,?_,?_,?_⟩
      · change ((T : M6)+s • E) *ᵥ e1 = 0
        simp only [Matrix.add_mulVec,Matrix.smul_mulVec,hTk1,hEker1,smul_zero,add_zero]
      · change ((T : M6)+s • E) *ᵥ e2 = 0
        simp only [Matrix.add_mulVec,Matrix.smul_mulVec,hTk2,hEker2,smul_zero,add_zero]
      · change Matrix.trace (G1*(((T : M6)+s • E).toBlocks₁₁)) = A1
        have hb : ((T : M6)+s • E).toBlocks₁₁ = (T : M6).toBlocks₁₁+s • E.toBlocks₁₁ := rfl
        rw [hb,Matrix.mul_add,Matrix.mul_smul,Matrix.trace_add,Matrix.trace_smul,
          hTrace1,smul_zero,add_zero]
        exact hT.2.2.2.1
      · change Matrix.trace (G2*(((T : M6)+s • E).toBlocks₂₂)) = A2
        have hb : ((T : M6)+s • E).toBlocks₂₂ = (T : M6).toBlocks₂₂+s • E.toBlocks₂₂ := rfl
        rw [hb,Matrix.mul_add,Matrix.mul_smul,Matrix.trace_add,Matrix.trace_smul,
          hTrace2,smul_zero,add_zero]
        exact hT.2.2.2.2
    have hPlus : T+t • Es ∈ C := hMember t (by rw [abs_of_pos ht])
    have hMinus : T-t • Es ∈ C := by
      simpa only [neg_smul,sub_eq_add_neg] using hMember (-t) (by rw [abs_neg,abs_of_pos ht])
    have hmid : T ∈ openSegment ℝ (T+t • Es) (T-t • Es) := mem_openSegment_add_sub T (t • Es)
    have heq : T+t • Es = T := ((mem_extremePoints.mp hExtreme).2 _ hPlus _ hMinus hmid).1
    have hzero : t • Es = 0 := add_eq_left.mp heq
    exact smul_ne_zero ht.ne' hEsne hzero
  obtain ⟨j,hj⟩ := hSome
  have hOthers (k : I6) (hk : k ≠ j) : lam k = 0 := by
    by_contra hn
    have hkpos : 0 < lam k := lt_of_le_of_ne (hLam k) (Ne.symm hn)
    exact hk (hUnique k j hkpos hj)
  have hOne : (T : M6) = lam j • Matrix.vecMulVec (u j) (u j) := by
    rw [hSpec]
    apply Finset.sum_eq_single j
    · intro k _ hk
      rw [hOthers k hk,zero_smul]
    · intro hn
      exact (hn (Finset.mem_univ j)).elim
  let v : V6 := Real.sqrt (lam j) • u j
  let v1 : V3 := fun i => v (Sum.inl i)
  let v2 : V3 := fun i => v (Sum.inr i)
  have hTvv : (T : M6) = Matrix.vecMulVec v v := by
    rw [hOne]
    ext r s
    have hs : (Real.sqrt (lam j))^2 = lam j := Real.sq_sqrt (hLam j)
    simp only [Matrix.smul_apply,Matrix.vecMulVec_apply,v,Pi.smul_apply,smul_eq_mul]
    nlinarith only [congrArg (fun c : ℝ => c*(u j r*u j s)) hs]
  have hv1ker : dotProduct ell1 v1 = 0 := by
    have hk := (hKernel j hj).1
    have h : dotProduct e1 v = 0 := by
      change dotProduct e1 (Real.sqrt (lam j) • u j) = 0
      rw [dotProduct_smul,hk,smul_zero]
    simpa only [e1,v1,dotProduct,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,
      Pi.zero_apply,zero_mul,Finset.sum_const_zero,add_zero] using h
  have hv2ker : dotProduct ell2 v2 = 0 := by
    have hk := (hKernel j hj).2
    have h : dotProduct e2 v = 0 := by
      change dotProduct e2 (Real.sqrt (lam j) • u j) = 0
      rw [dotProduct_smul,hk,smul_zero]
    simpa only [e2,v2,dotProduct,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,
      Pi.zero_apply,zero_mul,Finset.sum_const_zero,zero_add] using h
  have hv1norm : dotProduct v1 (G1 *ᵥ v1) = A1 := by
    have h := hT.2.2.2.1
    rw [hTvv] at h
    change Matrix.trace (G1*Matrix.vecMulVec v1 v1) = A1 at h
    rwa [hRankTrace] at h
  have hv2norm : dotProduct v2 (G2 *ᵥ v2) = A2 := by
    have h := hT.2.2.2.2
    rw [hTvv] at h
    change Matrix.trace (G2*Matrix.vecMulVec v2 v2) = A2 at h
    rwa [hRankTrace] at h
  refine ⟨v1,⟨hv1ker,hv1norm⟩,v2,⟨hv2ker,hv2norm⟩,T,?_,hT,?_⟩
  · have he : Sum.elim v1 v2 = v := by ext (i|i) <;> rfl
    rwa [he]
  · intro S hS
    change f T ≤ f S
    exact hMin S hS

end OAI.AnisotropicCalderon.ProductHessianSeparation

#print axioms OAI.AnisotropicCalderon.ProductHessianSeparation.productMetricMomentSection
#print axioms OAI.AnisotropicCalderon.ProductHessianSeparation.tangentMetricMomentSection
#print axioms OAI.AnisotropicCalderon.ProductHessianSeparation.isCompact_productMetricMomentSection
#print axioms OAI.AnisotropicCalderon.ProductHessianSeparation.exists_pos_normal_tangent_decomposition
#print axioms OAI.AnisotropicCalderon.ProductHessianSeparation.exists_rankOne_minimizer_tangentMetricMomentSection


