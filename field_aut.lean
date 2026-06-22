import Final_Project.cong_subgroup
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.RingTheory.LocalRing.Defs
import Mathlib.RingTheory.LocalRing.ResidueField.Defs
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Determinant

open Matrix BigOperators
open scoped MatrixGroups
noncomputable section



abbrev GL3 (A : Type*) [CommRing A] : Type _ :=
  GL (Fin 3) A



variable (R : Type*) [CommRing R] [Invertible (2 : R)]



abbrev AutSL3 : Type _ :=
  SL3 R ≃* SL3 R



def ringAutMapSL3 (σ : R ≃+* R) (x : SL3 R) : SL3 R :=
  ⟨((x : Matrix (Fin 3) (Fin 3) R).map σ), by
    -- Need determinant compatibility with entrywise ring automorphisms.
   calc
      ((x : Matrix (Fin 3) (Fin 3) R).map ⇑σ).det
          = σ ((x : Matrix (Fin 3) (Fin 3) R).det) := by
              simpa only [RingEquiv.mapMatrix_apply] using
                (σ.map_det
                  (x : Matrix (Fin 3) (Fin 3) R)).symm
      _ = 1 := by simp [x.property]⟩


def ringAutSL3 (σ : R ≃+* R) : AutSL3 R where
  toFun := ringAutMapSL3 R σ
  invFun := ringAutMapSL3 R σ.symm

  left_inv := by
    intro x
    apply Subtype.ext
    dsimp [ringAutMapSL3]
    simp
    ext i j
    dsimp [map]
    exact RingEquiv.symm_apply_apply σ _



  right_inv := by
    intro x
    apply Subtype.ext
    dsimp [ringAutMapSL3]
    simp
    ext i j
    dsimp [map]
    exact RingEquiv.symm_apply_apply σ.symm _


  map_mul' := by
    intro x y
    apply Subtype.ext
    ext i j
    simp [ringAutMapSL3, Matrix.mul_apply]



def innerAutSL3byGL3 (g : GL3 R) : MulAut (SL3 R) where
  toFun := fun x => ⟨g * Matrix.SpecialLinearGroup.toGL x * g⁻¹, by
    simp [Matrix.det_mul,  Ring.mul_inverse_cancel]⟩
  invFun := fun x =>⟨g⁻¹ * Matrix.SpecialLinearGroup.toGL x * g, by
    simp [Matrix.det_mul, Ring.inverse_mul_cancel]⟩

  left_inv := by
    intro x
    simp [mul_assoc]

  right_inv := by
    intro x
    simp [mul_assoc]

  map_mul' := by
    intro x y
    apply Subtype.ext
    simp [mul_assoc]

def invTransposeMap (x : SL3 R) : SL3 R :=
  ⟨(((x⁻¹ : SL3 R) : Matrix (Fin 3) (Fin 3) R).transpose), by
    rw [Matrix.det_transpose]
    exact (x⁻¹ : SL3 R).property⟩


def invTransposeAutSL3 : AutSL3 R where
  toFun := invTransposeMap R
  invFun := invTransposeMap R

  left_inv := by
    intro x
    apply Subtype.ext
    simp only [
    invTransposeMap,
    Matrix.SpecialLinearGroup.coe_mk,
    Matrix.SpecialLinearGroup.coe_inv
    ]
    rw [← Matrix.adjugate_transpose]
    simp only [Matrix.transpose_transpose]
    rw [Matrix.adjugate_adjugate _ (by decide)]
    simp [x.property]

  right_inv := by
    intro x
    apply Subtype.ext
    simp only [
    invTransposeMap,
    Matrix.SpecialLinearGroup.coe_mk,
    Matrix.SpecialLinearGroup.coe_inv
    ]
    rw [← Matrix.adjugate_transpose]
    simp only [Matrix.transpose_transpose]

    rw [Matrix.adjugate_adjugate _ (by decide)]
    simp [x.property]

  map_mul' := by
    intro x y
    apply Subtype.ext
    simp [invTransposeMap, Matrix.transpose_mul]










namespace FieldAutomorpisms


variable (F : Type*) [Field F] [Invertible (2 : F)]





/-! ### Block 3, Step 1: standard generators and basic `SL3`-level facts

`d1, d2, d3` are the three diagonal involutions from lecture 9.12.1. We record their
elementary algebraic relations (`d1*d1 = 1`, `d1*d2 = d3`, ...) and the same facts
lifted through an arbitrary automorphism `φ` (`phi_d1_mul_self`, `phi_d1_ne_one`, ...).
The end goal of this whole section is `diag_preserved_after_change_of_basis`: a basis
change `g` that turns `φ(d1), φ(d2), φ(d3)` back into `d1, d2, d3`. -/

def d1 : Matrix (Fin 3) (Fin 3) (R) :=
  Matrix.diagonal ![1, -1, -1]

def d2 : Matrix (Fin 3) (Fin 3) (R) :=
  Matrix.diagonal ![-1, 1, -1]

def d3 : Matrix (Fin 3) (Fin 3) (R) :=
  Matrix.diagonal ![-1, -1, 1]

def d1SL : SL3 R :=
  ⟨d1 R, by
    simp [d1, Matrix.det_diagonal, Fin.prod_univ_three]
  ⟩

def d2SL : SL3 R :=
  ⟨d2 R, by
    simp [d2, Matrix.det_diagonal, Fin.prod_univ_three]
  ⟩

def d3SL : SL3 R :=
  ⟨d3 R, by
    simp [d3, Matrix.det_diagonal, Fin.prod_univ_three]
  ⟩

omit [Invertible (2 : F)] in
/-- d1 is an involution. -/
theorem d1_mul_d1 : d1SL F * d1SL F = 1 := by
  apply Subtype.ext
  show d1 F * d1 F = (1 : Matrix (Fin 3) (Fin 3) F)
  unfold d1
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.diagonal_apply]

omit [Invertible (2 : F)] in
/-- d2 is an involution. -/
theorem d2_mul_d2 : d2SL F * d2SL F = 1 := by
  apply Subtype.ext
  show d2 F * d2 F = (1 : Matrix (Fin 3) (Fin 3) F)
  unfold d2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.diagonal_apply]

omit [Invertible (2 : F)] in
/-- d3 is an involution. -/
theorem d3_mul_d3 : d3SL F * d3SL F = 1 := by
  apply Subtype.ext
  show d3 F * d3 F = (1 : Matrix (Fin 3) (Fin 3) F)
  unfold d3
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.diagonal_apply]

omit [Invertible (2 : F)] in
/-- d1 and d2 commute. -/
theorem d1_mul_d2_comm : d1SL F * d2SL F = d2SL F * d1SL F := by
  apply Subtype.ext
  show d1 F * d2 F = d2 F * d1 F
  unfold d1 d2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.diagonal_apply]

omit [Invertible (2 : F)] in
/-- d1 * d2 = d3. -/
theorem d1_mul_d2_eq_d3 : d1SL F * d2SL F = d3SL F := by
  apply Subtype.ext
  show d1 F * d2 F = d3 F
  unfold d1 d2 d3
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.diagonal_apply]
/-- d1 is nontrivial. -/
theorem d1SL_ne_one : d1SL F ≠ 1 := by
  intro h
  have h11 : (d1 F) 1 1 = (1 : Matrix (Fin 3) (Fin 3) F) 1 1 :=
    congrArg (fun A : SL3 F => (A : Matrix (Fin 3) (Fin 3) F) 1 1) h
  simp [d1] at h11
  -- h11 : (-1 : F) = 1
  have step : (-1 : F) + 1 = 1 + 1 := congrArg (· + 1) h11
  have lhs0 : (-1 : F) + 1 = 0 := by ring
  have rhs2 : (1 : F) + 1 = 2 := by ring
  rw [lhs0, rhs2] at step
  exact (Invertible.ne_zero (2 : F)) step.symm

  /-- d2 is nontrivial. -/
  theorem d2SL_ne_one : d2SL F ≠ 1 := by
  intro h
  have h00 : (d2 F) 0 0 = (1 : Matrix (Fin 3) (Fin 3) F) 0 0 :=
    congrArg (fun A : SL3 F => (A : Matrix (Fin 3) (Fin 3) F) 0 0) h
  simp [d2] at h00
  have step : (-1 : F) + 1 = 1 + 1 := congrArg (· + 1) h00
  have lhs0 : (-1 : F) + 1 = 0 := by ring
  have rhs2 : (1 : F) + 1 = 2 := by ring
  rw [lhs0, rhs2] at step
  exact (Invertible.ne_zero (2 : F)) step.symm

 /-- d3 is nontrivial. -/
theorem d3SL_ne_one : d3SL F ≠ 1 := by
  intro h
  have h00 : (d3 F) 0 0 = (1 : Matrix (Fin 3) (Fin 3) F) 0 0 :=
    congrArg (fun A : SL3 F => (A : Matrix (Fin 3) (Fin 3) F) 0 0) h
  simp [d3] at h00
  have step : (-1 : F) + 1 = 1 + 1 := congrArg (· + 1) h00
  have lhs0 : (-1 : F) + 1 = 0 := by ring
  have rhs2 : (1 : F) + 1 = 2 := by ring
  rw [lhs0, rhs2] at step
  exact (Invertible.ne_zero (2 : F)) step.symm


omit [Invertible (2 : F)] in
theorem phi_d1_mul_self (φ : AutSL3 F) :
    φ (d1SL F) * φ (d1SL F) = 1 := by
  rw [← map_mul, d1_mul_d1, map_one]

omit [Invertible (2 : F)] in
theorem phi_d2_mul_self (φ : AutSL3 F) :
    φ (d2SL F) * φ (d2SL F) = 1 := by
  rw [← map_mul, d2_mul_d2, map_one]

omit [Invertible (2 : F)] in
theorem phi_d3_mul_self (φ : AutSL3 F) :
    φ (d3SL F) * φ (d3SL F) = 1 := by
  rw [← map_mul, d3_mul_d3, map_one]

theorem phi_d1_ne_one (φ : AutSL3 F) :
    φ (d1SL F) ≠ 1 := by
  intro h
  exact d1SL_ne_one F (φ.injective (h.trans (map_one φ).symm))

theorem phi_d2_ne_one (φ : AutSL3 F) :
    φ (d2SL F) ≠ 1 := by
  intro h
  exact d2SL_ne_one F (φ.injective (h.trans (map_one φ).symm))

theorem phi_d3_ne_one (φ : AutSL3 F) :
    φ (d3SL F) ≠ 1 := by
  intro h
  exact d3SL_ne_one F (φ.injective (h.trans (map_one φ).symm))

omit [Invertible (2 : F)] in
theorem phi_d1_d2_comm (φ : AutSL3 F) :
    φ (d1SL F) * φ (d2SL F) = φ (d2SL F) * φ (d1SL F) := by
  rw [← map_mul, ← map_mul, d1_mul_d2_comm]

omit [Invertible (2 : F)] in
theorem phi_d1_d2_eq_d3 (φ : AutSL3 F) :
    φ (d1SL F) * φ (d2SL F) = φ (d3SL F) := by
  rw [← map_mul, d1_mul_d2_eq_d3]


omit [Invertible (2 : F)] in
/-- The matrix-level version of `phi_d1_mul_self`. -/
theorem tau1_mul_self (φ : AutSL3 F) :
    (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F) *
      (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F) = 1 := by
  have h := phi_d1_mul_self F φ
  have hcoe := congrArg (fun A : SL3 F => (A : Matrix (Fin 3) (Fin 3) F)) h
  simpa using hcoe

theorem tau1_ne_neg_one (φ : AutSL3 F) :
    (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F) ≠ -1 := by
  intro h
  have hdet : (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F).det = 1 :=
    Matrix.SpecialLinearGroup.det_coe (φ (d1SL F))
  rw [h, show (-1 : Matrix (Fin 3) (Fin 3) F) = (-1 : F) • (1 : Matrix (Fin 3) (Fin 3) F) from
    (neg_one_smul F (1 : Matrix (Fin 3) (Fin 3) F)).symm,
    Matrix.det_smul, Matrix.det_one, mul_one] at hdet
  have h3 : ((-1 : F)) ^ (Fintype.card (Fin 3)) = -1 := Odd.neg_one_pow (by decide)
  rw [h3] at hdet
  -- hdet : (-1 : F) = 1
  have step : (-1 : F) + 1 = 1 + 1 := congrArg (· + 1) hdet
  have lhs0 : (-1 : F) + 1 = 0 := by ring
  have rhs2 : (1 : F) + 1 = 2 := by ring
  rw [lhs0, rhs2] at step
  exact (Invertible.ne_zero (2 : F)) step.symm

theorem tau1_ne_one (φ : AutSL3 F) :
    (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F) ≠ 1 := by
  intro h
  apply phi_d1_ne_one F φ
  apply Subtype.ext
  simpa using h

omit [Invertible (2 : F)] in
/-- Standard basis vectors of `Fin 3 → F`. Used much later to read off the columns of
the change-of-basis matrix `g` (see `gMatrix`). -/
def e1 : Fin 3 → F := ![1, 0, 0]

omit [Invertible (2 : F)] in
def e2 : Fin 3 → F := ![0, 1, 0]

omit [Invertible (2 : F)] in
def e3 : Fin 3 → F := ![0, 0, 1]

/-! ### Idempotent decomposition for an arbitrary involution `τ`

If `τ * τ = 1` and `char F ≠ 2`, then `p = (1+τ)/2` and `q = (1-τ)/2` are complementary
idempotents (`p+q=1`, `pq=qp=0`, `p²=p`, `q²=q`) whose ranges are exactly the `+1` and
`-1` eigenspaces of `τ`. We build this *once* for a generic matrix `τ`, instead of
repeating it separately for `τ1 = φ(d1)`, `τ2 = φ(d2)`, `τ3 = φ(d3)`, and specialize
three times below (`finrank_range_pIdemLin_tau3_eq_one`, etc.). -/

noncomputable def pIdem (τ : Matrix (Fin 3) (Fin 3) F) : Matrix (Fin 3) (Fin 3) F :=
  (2 : F)⁻¹ • (1 + τ)

noncomputable def qIdem (τ : Matrix (Fin 3) (Fin 3) F) : Matrix (Fin 3) (Fin 3) F :=
  (2 : F)⁻¹ • (1 - τ)

theorem pIdem_idem (τ : Matrix (Fin 3) (Fin 3) F) (hτ2 : τ * τ = 1) :
    pIdem F τ * pIdem F τ = pIdem F τ := by
  have key : (1 + τ) * (1 + τ) = (2 : F) • (1 + τ) := by
    rw [mul_add, add_mul, add_mul]
    simp only [one_mul, mul_one, hτ2]
    rw [two_smul]
    abel
  unfold pIdem
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, key, smul_smul]
  congr 1
  field_simp

theorem qIdem_idem (τ : Matrix (Fin 3) (Fin 3) F) (hτ2 : τ * τ = 1) :
    qIdem F τ * qIdem F τ = qIdem F τ := by
  have key : (1 - τ) * (1 - τ) = (2 : F) • (1 - τ) := by
    rw [mul_sub, sub_mul, sub_mul]
    simp only [one_mul, mul_one, hτ2]
    rw [two_smul]
    abel
  unfold qIdem
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, key, smul_smul]
  congr 1
  field_simp

theorem pIdem_add_qIdem (τ : Matrix (Fin 3) (Fin 3) F) :
    pIdem F τ + qIdem F τ = 1 := by
  unfold pIdem qIdem
  rw [← smul_add]
  have hsum : (1 + τ) + (1 - τ) = (2 : F) • (1 : Matrix (Fin 3) (Fin 3) F) := by
    rw [two_smul]; abel
  rw [hsum, smul_smul, inv_mul_cancel₀ (Invertible.ne_zero (2 : F)), one_smul]

omit [Invertible (2 : F)] in
theorem pIdem_mul_qIdem (τ : Matrix (Fin 3) (Fin 3) F) (hτ2 : τ * τ = 1) :
    pIdem F τ * qIdem F τ = 0 := by
  have key : (1 + τ) * (1 - τ) = 0 := by
    rw [mul_sub, add_mul, add_mul]
    simp only [one_mul, mul_one, hτ2]
    abel
  unfold pIdem qIdem
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, key, smul_zero]

omit [Invertible (2 : F)] in
theorem qIdem_mul_pIdem (τ : Matrix (Fin 3) (Fin 3) F) (hτ2 : τ * τ = 1) :
    qIdem F τ * pIdem F τ = 0 := by
  have key : (1 - τ) * (1 + τ) = 0 := by
    rw [sub_mul, mul_add, mul_add]
    simp only [one_mul, mul_one, hτ2]
    abel
  unfold qIdem pIdem
  rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, key, smul_zero]

theorem pIdem_sub_qIdem (τ : Matrix (Fin 3) (Fin 3) F) :
    pIdem F τ - qIdem F τ = τ := by
  unfold pIdem qIdem
  rw [← smul_sub]
  have key : (1 + τ) - (1 - τ) = (2 : F) • τ := by
    rw [two_smul]; abel
  rw [key, smul_smul, inv_mul_cancel₀ (Invertible.ne_zero (2 : F)), one_smul]

noncomputable def pIdemLin (τ : Matrix (Fin 3) (Fin 3) F) : Module.End F (Fin 3 → F) :=
  Matrix.toLinAlgEquiv' (pIdem F τ)

noncomputable def qIdemLin (τ : Matrix (Fin 3) (Fin 3) F) : Module.End F (Fin 3 → F) :=
  Matrix.toLinAlgEquiv' (qIdem F τ)

noncomputable def tauLin (τ : Matrix (Fin 3) (Fin 3) F) : Module.End F (Fin 3 → F) :=
  Matrix.toLinAlgEquiv' τ

theorem pIdemLin_idem (τ : Matrix (Fin 3) (Fin 3) F) (hτ2 : τ * τ = 1) :
    IsIdempotentElem (pIdemLin F τ) := by
  show pIdemLin F τ * pIdemLin F τ = pIdemLin F τ
  unfold pIdemLin
  rw [← map_mul, pIdem_idem F τ hτ2]

theorem qIdemLin_idem (τ : Matrix (Fin 3) (Fin 3) F) (hτ2 : τ * τ = 1) :
    IsIdempotentElem (qIdemLin F τ) := by
  show qIdemLin F τ * qIdemLin F τ = qIdemLin F τ
  unfold qIdemLin
  rw [← map_mul, qIdem_idem F τ hτ2]

theorem pIdemLin_add_qIdemLin (τ : Matrix (Fin 3) (Fin 3) F) :
    pIdemLin F τ + qIdemLin F τ = 1 := by
  unfold pIdemLin qIdemLin
  rw [← map_add, pIdem_add_qIdem, Matrix.toLinAlgEquiv'_one]
  rfl

omit [Invertible (2 : F)] in
theorem pIdemLin_mul_qIdemLin (τ : Matrix (Fin 3) (Fin 3) F) (hτ2 : τ * τ = 1) :
    pIdemLin F τ * qIdemLin F τ = 0 := by
  show pIdemLin F τ * qIdemLin F τ = 0
  unfold pIdemLin qIdemLin
  rw [← map_mul, pIdem_mul_qIdem F τ hτ2, map_zero]

theorem pIdemLin_sub_qIdemLin (τ : Matrix (Fin 3) (Fin 3) F) :
    pIdemLin F τ - qIdemLin F τ = tauLin F τ := by
  unfold pIdemLin qIdemLin tauLin
  rw [← map_sub, pIdem_sub_qIdem]

theorem tauLin_mul_qIdemLin (τ : Matrix (Fin 3) (Fin 3) F) (hτ2 : τ * τ = 1) :
    tauLin F τ * qIdemLin F τ = -qIdemLin F τ := by
  rw [← pIdemLin_sub_qIdemLin, sub_mul, pIdemLin_mul_qIdemLin F τ hτ2, qIdemLin_idem F τ hτ2,
    zero_sub]

theorem ker_pIdemLin_eq_range_qIdemLin (τ : Matrix (Fin 3) (Fin 3) F) (hτ2 : τ * τ = 1) :
    LinearMap.ker (pIdemLin F τ) = LinearMap.range (qIdemLin F τ) := by
  have hq : qIdemLin F τ = 1 - pIdemLin F τ := by
    have h := pIdemLin_add_qIdemLin F τ
    have := congrArg (fun x => x - pIdemLin F τ) h
    simpa using this
  rw [hq]
  exact LinearMap.IsIdempotentElem.ker_eq_range_one_sub (pIdemLin_idem F τ hτ2)

theorem isCompl_range_pIdemLin_range_qIdemLin (τ : Matrix (Fin 3) (Fin 3) F) (hτ2 : τ * τ = 1) :
    IsCompl (LinearMap.range (pIdemLin F τ)) (LinearMap.range (qIdemLin F τ)) := by
  rw [← ker_pIdemLin_eq_range_qIdemLin F τ hτ2]
  exact LinearMap.IsIdempotentElem.isCompl (pIdemLin_idem F τ hτ2)

theorem finrank_range_pIdemLin_add_finrank_range_qIdemLin
    (τ : Matrix (Fin 3) (Fin 3) F) (hτ2 : τ * τ = 1) :
    Module.finrank F (LinearMap.range (pIdemLin F τ)) +
      Module.finrank F (LinearMap.range (qIdemLin F τ)) = 3 := by
  rw [Submodule.finrank_add_eq_of_isCompl (isCompl_range_pIdemLin_range_qIdemLin F τ hτ2),
    Module.finrank_fin_fun]

theorem tau_ne_neg_one_of_det (τ : Matrix (Fin 3) (Fin 3) F) (hdet : τ.det = 1) :
    τ ≠ -1 := by
  intro h
  rw [h, show (-1 : Matrix (Fin 3) (Fin 3) F) = (-1 : F) • (1 : Matrix (Fin 3) (Fin 3) F) from
    (neg_one_smul F (1 : Matrix (Fin 3) (Fin 3) F)).symm,
    Matrix.det_smul, Matrix.det_one, mul_one] at hdet
  have h3 : ((-1 : F)) ^ (Fintype.card (Fin 3)) = -1 := Odd.neg_one_pow (by decide)
  rw [h3] at hdet
  have step : (-1 : F) + 1 = 1 + 1 := congrArg (· + 1) hdet
  have lhs0 : (-1 : F) + 1 = 0 := by ring
  have rhs0 : (1 : F) + 1 = 2 := by ring
  rw [lhs0, rhs0] at step
  exact (Invertible.ne_zero (2 : F)) step.symm

theorem pIdem_ne_zero (τ : Matrix (Fin 3) (Fin 3) F) (hdet : τ.det = 1) :
    pIdem F τ ≠ 0 := by
  intro h
  unfold pIdem at h
  rcases smul_eq_zero.mp h with h2 | h2
  · exact (inv_ne_zero (Invertible.ne_zero (2 : F))) h2
  · exact tau_ne_neg_one_of_det F τ hdet (eq_neg_of_add_eq_zero_right h2)

theorem qIdem_ne_zero (τ : Matrix (Fin 3) (Fin 3) F) (hτ1 : τ ≠ 1) :
    qIdem F τ ≠ 0 := by
  intro h
  unfold qIdem at h
  rcases smul_eq_zero.mp h with h2 | h2
  · exact (inv_ne_zero (Invertible.ne_zero (2 : F))) h2
  · exact hτ1 (sub_eq_zero.mp h2).symm

theorem pIdemLin_ne_zero (τ : Matrix (Fin 3) (Fin 3) F) (hdet : τ.det = 1) :
    pIdemLin F τ ≠ 0 := by
  unfold pIdemLin
  intro h
  apply pIdem_ne_zero F τ hdet
  apply Matrix.toLinAlgEquiv'.injective
  rw [h, map_zero]

theorem qIdemLin_ne_zero (τ : Matrix (Fin 3) (Fin 3) F) (hτ1 : τ ≠ 1) :
    qIdemLin F τ ≠ 0 := by
  unfold qIdemLin
  intro h
  apply qIdem_ne_zero F τ hτ1
  apply Matrix.toLinAlgEquiv'.injective
  rw [h, map_zero]

theorem range_pIdemLin_ne_bot (τ : Matrix (Fin 3) (Fin 3) F) (hdet : τ.det = 1) :
    LinearMap.range (pIdemLin F τ) ≠ ⊥ := by
  rw [Ne, LinearMap.range_eq_bot]; exact pIdemLin_ne_zero F τ hdet

theorem range_qIdemLin_ne_bot (τ : Matrix (Fin 3) (Fin 3) F) (hτ1 : τ ≠ 1) :
    LinearMap.range (qIdemLin F τ) ≠ ⊥ := by
  rw [Ne, LinearMap.range_eq_bot]; exact qIdemLin_ne_zero F τ hτ1

theorem finrank_range_pIdemLin_pos (τ : Matrix (Fin 3) (Fin 3) F) (hdet : τ.det = 1) :
    0 < Module.finrank F (LinearMap.range (pIdemLin F τ)) := by
  rw [Module.finrank_pos_iff, Submodule.nontrivial_iff_ne_bot]
  exact range_pIdemLin_ne_bot F τ hdet

theorem finrank_range_qIdemLin_pos (τ : Matrix (Fin 3) (Fin 3) F) (hτ1 : τ ≠ 1) :
    0 < Module.finrank F (LinearMap.range (qIdemLin F τ)) := by
  rw [Module.finrank_pos_iff, Submodule.nontrivial_iff_ne_bot]
  exact range_qIdemLin_ne_bot F τ hτ1

theorem range_qIdemLin_invariant (τ : Matrix (Fin 3) (Fin 3) F) (hτ2 : τ * τ = 1) :
    LinearMap.range (qIdemLin F τ) ≤ (LinearMap.range (qIdemLin F τ)).comap (tauLin F τ) := by
  rintro x ⟨y, rfl⟩
  show tauLin F τ (qIdemLin F τ y) ∈ LinearMap.range (qIdemLin F τ)
  have heq : tauLin F τ (qIdemLin F τ y) = -qIdemLin F τ y :=
    LinearMap.congr_fun (tauLin_mul_qIdemLin F τ hτ2) y
  rw [heq]
  exact ⟨-y, by rw [map_neg]⟩

theorem tauLin_eq_one_sub_two_smul_qIdemLin (τ : Matrix (Fin 3) (Fin 3) F) :
    tauLin F τ = 1 - (2 : F) • qIdemLin F τ := by
  rw [← pIdemLin_sub_qIdemLin]
  have hp1 : pIdemLin F τ = 1 - qIdemLin F τ := by
    have h := pIdemLin_add_qIdemLin F τ
    have := congrArg (fun x => x - qIdemLin F τ) h
    simpa using this
  rw [hp1, two_smul]
  abel

theorem range_qIdemLin_mapQ_eq_id (τ : Matrix (Fin 3) (Fin 3) F) (hτ2 : τ * τ = 1) :
    (LinearMap.range (qIdemLin F τ)).mapQ (LinearMap.range (qIdemLin F τ)) (tauLin F τ)
      (range_qIdemLin_invariant F τ hτ2) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  refine Submodule.Quotient.induction_on _ x (fun y => ?_)
  simp only [Submodule.mapQ_apply, LinearMap.id_apply, Submodule.Quotient.eq]
  have hy : tauLin F τ y = y - (2 : F) • qIdemLin F τ y := by
    rw [tauLin_eq_one_sub_two_smul_qIdemLin]; rfl
  have hdiff : tauLin F τ y - y = -((2 : F) • qIdemLin F τ y) := by
    rw [hy]; abel
  rw [hdiff]
  exact Submodule.neg_mem _ (Submodule.smul_mem _ _ ⟨y, rfl⟩)

theorem tauLin_restrict_eq_neg_one (τ : Matrix (Fin 3) (Fin 3) F) (hτ2 : τ * τ = 1)
    (he : ∀ x ∈ LinearMap.range (qIdemLin F τ), tauLin F τ x ∈ LinearMap.range (qIdemLin F τ)) :
    (tauLin F τ).restrict he = -1 := by
  apply LinearMap.ext
  rintro ⟨x, y, rfl⟩
  apply Subtype.ext
  show tauLin F τ (qIdemLin F τ y) = -(qIdemLin F τ y)
  exact LinearMap.congr_fun (tauLin_mul_qIdemLin F τ hτ2) y

omit [Invertible (2 : F)] in
theorem det_neg_one_end_range_qIdemLin (τ : Matrix (Fin 3) (Fin 3) F) :
    LinearMap.det (-1 : Module.End F (LinearMap.range (qIdemLin F τ))) =
      (-1 : F) ^ Module.finrank F (LinearMap.range (qIdemLin F τ)) := by
  have hrw : (-1 : Module.End F (LinearMap.range (qIdemLin F τ))) =
      (-1 : F) • (1 : Module.End F (LinearMap.range (qIdemLin F τ))) :=
    (neg_one_smul F (1 : Module.End F (LinearMap.range (qIdemLin F τ)))).symm
  have hone : LinearMap.det (1 : Module.End F (LinearMap.range (qIdemLin F τ))) = 1 := by
    rw [show (1 : Module.End F (LinearMap.range (qIdemLin F τ))) = LinearMap.id from rfl,
      LinearMap.det_id]
  rw [hrw, LinearMap.det_smul, hone, mul_one]

theorem det_tauLin_eq (τ : Matrix (Fin 3) (Fin 3) F) (hτ2 : τ * τ = 1) :
    LinearMap.det (tauLin F τ) =
      (-1 : F) ^ Module.finrank F (LinearMap.range (qIdemLin F τ)) := by
  rw [LinearMap.det_eq_det_mul_det (LinearMap.range (qIdemLin F τ)) (tauLin F τ)
      (range_qIdemLin_invariant F τ hτ2),
    tauLin_restrict_eq_neg_one F τ hτ2, det_neg_one_end_range_qIdemLin,
    range_qIdemLin_mapQ_eq_id F τ hτ2, LinearMap.det_id, mul_one]

omit [Invertible (2 : F)] in
theorem toLinAlgEquiv'_eq_toLin' (M : Matrix (Fin 3) (Fin 3) F) :
    (Matrix.toLinAlgEquiv' M : Module.End F (Fin 3 → F)) = Matrix.toLin' M := by
  apply LinearMap.ext
  intro v
  rw [Matrix.toLinAlgEquiv'_apply, Matrix.toLin'_apply]

omit [Invertible (2 : F)] in
theorem det_tauLin_eq_det (τ : Matrix (Fin 3) (Fin 3) F) :
    LinearMap.det (tauLin F τ) = τ.det := by
  unfold tauLin
  rw [toLinAlgEquiv'_eq_toLin', LinearMap.det_toLin']

theorem finrank_range_qIdemLin_eq_two
    (τ : Matrix (Fin 3) (Fin 3) F) (hτ2 : τ * τ = 1) (hτ1 : τ ≠ 1) (hdet : τ.det = 1) :
    Module.finrank F (LinearMap.range (qIdemLin F τ)) = 2 := by
  have h1 := det_tauLin_eq F τ hτ2
  have h2 := det_tauLin_eq_det F τ
  rw [h2, hdet] at h1
  have hle : Module.finrank F (LinearMap.range (qIdemLin F τ)) ≤ 2 := by
    have hsum := finrank_range_pIdemLin_add_finrank_range_qIdemLin F τ hτ2
    have hpos := finrank_range_pIdemLin_pos F τ hdet
    omega
  have hpos := finrank_range_qIdemLin_pos F τ hτ1
  have hcases : Module.finrank F (LinearMap.range (qIdemLin F τ)) = 1 ∨
      Module.finrank F (LinearMap.range (qIdemLin F τ)) = 2 := by omega
  rcases hcases with h | h
  · rw [h] at h1
    simp at h1
    have step : (1 : F) + 1 = (-1 : F) + 1 := congrArg (· + 1) h1
    have lhs2 : (1 : F) + 1 = 2 := by ring
    have rhs0 : (-1 : F) + 1 = 0 := by ring
    rw [lhs2, rhs0] at step
    exact absurd step (Invertible.ne_zero (2 : F))
  · exact h

theorem finrank_range_pIdemLin_eq_one
    (τ : Matrix (Fin 3) (Fin 3) F) (hτ2 : τ * τ = 1) (hτ1 : τ ≠ 1) (hdet : τ.det = 1) :
    Module.finrank F (LinearMap.range (pIdemLin F τ)) = 1 := by
  have hsum := finrank_range_pIdemLin_add_finrank_range_qIdemLin F τ hτ2
  have h2 := finrank_range_qIdemLin_eq_two F τ hτ2 hτ1 hdet
  omega

omit [Invertible (2 : F)] in
/-! ### Specializing the generic `τ`-machinery to `τ1 = φ(d1)`, `τ2 = φ(d2)`, `τ3 = φ(d3)`

`tau1_mul_self`/`tau1_ne_one`/`tau1_ne_neg_one` (defined earlier, specific to `d1`)
already give the three hypotheses the generic lemmas need. `sl3_mul_self_matrix` and
`sl3_ne_one_matrix` lift the analogous group-level facts for `d2`, `d3` down to the
matrix level, so we get `finrank(range pIdemLin τᵢ) = 1` and `= 2` for the `-1`-side,
for all three `i = 1, 2, 3`, essentially for free. -/

omit [Invertible (2 : F)] in
theorem sl3_mul_self_matrix {A : SL3 F} (h : A * A = 1) :
    (A : Matrix (Fin 3) (Fin 3) F) * (A : Matrix (Fin 3) (Fin 3) F) = 1 := by
  have hcoe := congrArg (fun B : SL3 F => (B : Matrix (Fin 3) (Fin 3) F)) h
  simpa using hcoe

omit [Invertible (2 : F)] in
theorem sl3_ne_one_matrix {A : SL3 F} (h : A ≠ 1) :
    (A : Matrix (Fin 3) (Fin 3) F) ≠ 1 := by
  intro hc
  exact h (Subtype.ext (by simpa using hc))

omit [Invertible (2 : F)] in
theorem tau2_mul_self (φ : AutSL3 F) :
    (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F) * (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F) = 1 :=
  sl3_mul_self_matrix F (phi_d2_mul_self F φ)

omit [Invertible (2 : F)] in
theorem tau3_mul_self (φ : AutSL3 F) :
    (φ (d3SL F) : Matrix (Fin 3) (Fin 3) F) * (φ (d3SL F) : Matrix (Fin 3) (Fin 3) F) = 1 :=
  sl3_mul_self_matrix F (phi_d3_mul_self F φ)

theorem tau2_ne_one (φ : AutSL3 F) :
    (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F) ≠ 1 :=
  sl3_ne_one_matrix F (phi_d2_ne_one F φ)

theorem tau3_ne_one (φ : AutSL3 F) :
    (φ (d3SL F) : Matrix (Fin 3) (Fin 3) F) ≠ 1 :=
  sl3_ne_one_matrix F (phi_d3_ne_one F φ)

theorem finrank_range_pIdemLin_tau3_eq_one (φ : AutSL3 F) :
    Module.finrank F (LinearMap.range (pIdemLin F (φ (d3SL F) : Matrix (Fin 3) (Fin 3) F))) = 1 :=
  finrank_range_pIdemLin_eq_one F _ (tau3_mul_self F φ) (tau3_ne_one F φ)
    (Matrix.SpecialLinearGroup.det_coe (φ (d3SL F)))

theorem finrank_range_qIdemLin_tau3_eq_two (φ : AutSL3 F) :
    Module.finrank F (LinearMap.range (qIdemLin F (φ (d3SL F) : Matrix (Fin 3) (Fin 3) F))) = 2 :=
  finrank_range_qIdemLin_eq_two F _ (tau3_mul_self F φ) (tau3_ne_one F φ)
    (Matrix.SpecialLinearGroup.det_coe (φ (d3SL F)))


/-! ### `τ1` and `τ2` commute, hence preserve each other's eigenspaces

This is the part that lets us go beyond "`τ1` alone is diagonalizable": since
`φ(d1)` and `φ(d2)` commute, each of `range(pIdemLin τ1)`, `range(qIdemLin τ1)` is
invariant under `τ2` (and under `pIdemLin τ2`/`qIdemLin τ2` individually). -/

omit [Invertible (2 : F)] in
theorem tau1_mul_tau2_comm (φ : AutSL3 F) :
    (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F) * (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F) =
      (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F) * (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F) := by
  have h := phi_d1_d2_comm F φ
  have hcoe := congrArg (fun A : SL3 F => (A : Matrix (Fin 3) (Fin 3) F)) h
  simpa using hcoe

omit [Invertible (2 : F)] in
theorem pIdem_tau1_mul_tau2_comm (φ : AutSL3 F) :
    pIdem F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F) * (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F) =
      (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F) * pIdem F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F) := by
  unfold pIdem
  rw [Matrix.smul_mul, Matrix.mul_smul]
  congr 1
  rw [add_mul, mul_add, one_mul, mul_one, tau1_mul_tau2_comm]

omit [Invertible (2 : F)] in
theorem qIdem_tau1_mul_tau2_comm (φ : AutSL3 F) :
    qIdem F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F) * (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F) =
      (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F) * qIdem F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F) := by
  unfold qIdem
  rw [Matrix.smul_mul, Matrix.mul_smul]
  congr 1
  rw [sub_mul, mul_sub, one_mul, mul_one, tau1_mul_tau2_comm]

omit [Invertible (2 : F)] in
theorem pIdemLin_tau1_mul_tau2Lin_comm (φ : AutSL3 F) :
    pIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F) *
        tauLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F) =
      tauLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F) *
        pIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F) := by
  show pIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F) *
        tauLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F) =
      tauLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F) *
        pIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)
  unfold pIdemLin tauLin
  rw [← map_mul, ← map_mul, pIdem_tau1_mul_tau2_comm]

omit [Invertible (2 : F)] in
theorem qIdemLin_tau1_mul_tau2Lin_comm (φ : AutSL3 F) :
    qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F) *
        tauLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F) =
      tauLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F) *
        qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F) := by
  show qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F) *
        tauLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F) =
      tauLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F) *
        qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)
  unfold qIdemLin tauLin
  rw [← map_mul, ← map_mul, qIdem_tau1_mul_tau2_comm]

omit [Invertible (2 : F)] in
theorem range_pIdemLin_tau1_invariant_tau2 (φ : AutSL3 F) :
    ∀ x ∈ LinearMap.range (pIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)),
      tauLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F) x ∈
        LinearMap.range (pIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) := by
  rintro x ⟨y, rfl⟩
  exact ⟨tauLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F) y,
    LinearMap.congr_fun (pIdemLin_tau1_mul_tau2Lin_comm F φ) y⟩

omit [Invertible (2 : F)] in
theorem range_qIdemLin_tau1_invariant_tau2 (φ : AutSL3 F) :
    ∀ x ∈ LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)),
      tauLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F) x ∈
        LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) := by
  rintro x ⟨y, rfl⟩
  exact ⟨tauLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F) y,
    LinearMap.congr_fun (qIdemLin_tau1_mul_tau2Lin_comm F φ) y⟩


omit [Invertible (2 : F)] in
theorem pIdemLin_apply_eq (τ : Matrix (Fin 3) (Fin 3) F) (x : Fin 3 → F) :
    pIdemLin F τ x = (2 : F)⁻¹ • (x + tauLin F τ x) := by
  unfold pIdemLin pIdem tauLin
  rw [map_smul, map_add, Matrix.toLinAlgEquiv'_one]
  rfl

omit [Invertible (2 : F)] in
theorem qIdemLin_apply_eq (τ : Matrix (Fin 3) (Fin 3) F) (x : Fin 3 → F) :
    qIdemLin F τ x = (2 : F)⁻¹ • (x - tauLin F τ x) := by
  unfold qIdemLin qIdem tauLin
  rw [map_smul, map_sub, Matrix.toLinAlgEquiv'_one]
  rfl

omit [Invertible (2 : F)] in
theorem range_pIdemLin_tau1_invariant_pIdemLin_tau2 (φ : AutSL3 F) :
    ∀ x ∈ LinearMap.range (pIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)),
      pIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F) x ∈
        LinearMap.range (pIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) := by
  intro x hx
  rw [pIdemLin_apply_eq]
  exact Submodule.smul_mem _ _ (Submodule.add_mem _ hx
    (range_pIdemLin_tau1_invariant_tau2 F φ x hx))

omit [Invertible (2 : F)] in
theorem range_pIdemLin_tau1_invariant_qIdemLin_tau2 (φ : AutSL3 F) :
    ∀ x ∈ LinearMap.range (pIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)),
      qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F) x ∈
        LinearMap.range (pIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) := by
  intro x hx
  rw [qIdemLin_apply_eq]
  exact Submodule.smul_mem _ _ (Submodule.sub_mem _ hx
    (range_pIdemLin_tau1_invariant_tau2 F φ x hx))

theorem range_pIdemLin_tau1_le_sup (φ : AutSL3 F) :
    LinearMap.range (pIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ≤
      (LinearMap.range (pIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
          LinearMap.range (pIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F))) ⊔
        (LinearMap.range (pIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
          LinearMap.range (qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F))) := by
  intro x hx
  have hsum : pIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F) x +
      qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F) x = x :=
    LinearMap.congr_fun (pIdemLin_add_qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)) x
  have h1 : pIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F) x ∈
      LinearMap.range (pIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (pIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)) :=
    ⟨range_pIdemLin_tau1_invariant_pIdemLin_tau2 F φ x hx, ⟨x, rfl⟩⟩
  have h2 : qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F) x ∈
      LinearMap.range (pIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)) :=
    ⟨range_pIdemLin_tau1_invariant_qIdemLin_tau2 F φ x hx, ⟨x, rfl⟩⟩
  rw [← hsum]
  exact Submodule.add_mem_sup h1 h2

omit [Invertible (2 : F)] in
theorem tau1_mul_tau2_eq_tau3 (φ : AutSL3 F) :
    (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F) * (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F) =
      (φ (d3SL F) : Matrix (Fin 3) (Fin 3) F) := by
  have h := phi_d1_d2_eq_d3 F φ
  have hcoe := congrArg (fun A : SL3 F => (A : Matrix (Fin 3) (Fin 3) F)) h
  simpa using hcoe

omit [Invertible (2 : F)] in
theorem tauLin_tau3_eq_mul (φ : AutSL3 F) :
    tauLin F (φ (d3SL F) : Matrix (Fin 3) (Fin 3) F) =
      tauLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F) *
        tauLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F) := by
  unfold tauLin
  rw [← map_mul, tau1_mul_tau2_eq_tau3]

omit [Invertible (2 : F)] in
theorem qIdemLin_mul_pIdemLin (τ : Matrix (Fin 3) (Fin 3) F) (hτ2 : τ * τ = 1) :
    qIdemLin F τ * pIdemLin F τ = 0 := by
  show qIdemLin F τ * pIdemLin F τ = 0
  unfold qIdemLin pIdemLin
  rw [← map_mul, qIdem_mul_pIdem F τ hτ2, map_zero]

theorem tauLin_mul_pIdemLin (τ : Matrix (Fin 3) (Fin 3) F) (hτ2 : τ * τ = 1) :
    tauLin F τ * pIdemLin F τ = pIdemLin F τ := by
  rw [← pIdemLin_sub_qIdemLin, sub_mul, pIdemLin_idem F τ hτ2, qIdemLin_mul_pIdemLin F τ hτ2,
    sub_zero]

theorem mem_range_pIdemLin_iff_eigen (τ : Matrix (Fin 3) (Fin 3) F) (hτ2 : τ * τ = 1) (v : Fin 3 → F) :
    v ∈ LinearMap.range (pIdemLin F τ) → tauLin F τ v = v := by
  rintro ⟨y, rfl⟩
  exact LinearMap.congr_fun (tauLin_mul_pIdemLin F τ hτ2) y

theorem mem_range_qIdemLin_iff_eigen (τ : Matrix (Fin 3) (Fin 3) F) (hτ2 : τ * τ = 1) (v : Fin 3 → F) :
    v ∈ LinearMap.range (qIdemLin F τ) → tauLin F τ v = -v := by
  rintro ⟨y, rfl⟩
  exact LinearMap.congr_fun (tauLin_mul_qIdemLin F τ hτ2) y

/-! ### Pinning down all four pairwise intersections via `τ3 = τ1 τ2`

We want `range(pIdemLin τ1) ⊓ range(pIdemLin τ2) = 0`, and the other three pairwise
intersections to each be 1-dimensional (these are exactly the lines spanned by
`v1, v2, v3` below). Redoing the idempotent argument *inside* a 2-dimensional
subspace would need the whole machinery above generalized to an arbitrary subspace.
Instead, we use `τ3 = τ1 τ2`, whose own `±1`-eigenspaces we already know the
dimensions of (1 and 2, from the previous section) as a referee: every pairwise
intersection embeds into a `±1`-eigenspace of `τ3`, which bounds its dimension, and a
short linear system on the four dimensions (`a+b=1`, `c+d=2`, `d≤1`, ...) pins each
one down exactly, without ever touching a genuine subspace-of-a-subspace argument. -/

theorem inf_q1_q2_le_p3 (φ : AutSL3 F) :
    LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)) ≤
      LinearMap.range (pIdemLin F (φ (d3SL F) : Matrix (Fin 3) (Fin 3) F)) := by
  intro v hv
  have h1 : tauLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F) v = -v :=
    mem_range_qIdemLin_iff_eigen F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F) (tau1_mul_self F φ) v hv.1
  have h2 : tauLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F) v = -v :=
    mem_range_qIdemLin_iff_eigen F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F) (tau2_mul_self F φ) v hv.2
  have h3 : tauLin F (φ (d3SL F) : Matrix (Fin 3) (Fin 3) F) v = v := by
    rw [tauLin_tau3_eq_mul]
    show tauLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)
      (tauLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F) v) = v
    rw [h2, map_neg, h1, neg_neg]
  refine ⟨v, ?_⟩
  rw [pIdemLin_apply_eq, h3]
  rw [show v + v = (2 : F) • v from (two_smul F v).symm, smul_smul,
    inv_mul_cancel₀ (Invertible.ne_zero (2 : F)), one_smul]

omit [Invertible (2 : F)] in
theorem range_qIdemLin_tau1_invariant_pIdemLin_tau2 (φ : AutSL3 F) :
    ∀ x ∈ LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)),
      pIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F) x ∈
        LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) := by
  intro x hx
  rw [pIdemLin_apply_eq]
  exact Submodule.smul_mem _ _ (Submodule.add_mem _ hx
    (range_qIdemLin_tau1_invariant_tau2 F φ x hx))

omit [Invertible (2 : F)] in
theorem range_qIdemLin_tau1_invariant_qIdemLin_tau2 (φ : AutSL3 F) :
    ∀ x ∈ LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)),
      qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F) x ∈
        LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) := by
  intro x hx
  rw [qIdemLin_apply_eq]
  exact Submodule.smul_mem _ _ (Submodule.sub_mem _ hx
    (range_qIdemLin_tau1_invariant_tau2 F φ x hx))

theorem range_qIdemLin_tau1_le_sup (φ : AutSL3 F) :
    LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ≤
      (LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
          LinearMap.range (pIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F))) ⊔
        (LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
          LinearMap.range (qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F))) := by
  intro x hx
  have hsum : pIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F) x +
      qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F) x = x :=
    LinearMap.congr_fun (pIdemLin_add_qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)) x
  have h1 : pIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F) x ∈
      LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (pIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)) :=
    ⟨range_qIdemLin_tau1_invariant_pIdemLin_tau2 F φ x hx, ⟨x, rfl⟩⟩
  have h2 : qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F) x ∈
      LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)) :=
    ⟨range_qIdemLin_tau1_invariant_qIdemLin_tau2 F φ x hx, ⟨x, rfl⟩⟩
  rw [← hsum]
  exact Submodule.add_mem_sup h1 h2

theorem finrank_inf_add_finrank_inf_p1 (φ : AutSL3 F) :
    Module.finrank F ↥(LinearMap.range (pIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (pIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F))) +
      Module.finrank F ↥(LinearMap.range (pIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F))) = 1 := by
  have hsup : (LinearMap.range (pIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (pIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F))) ⊔
      (LinearMap.range (pIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F))) =
      LinearMap.range (pIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) := by
    apply le_antisymm
    · exact sup_le inf_le_left inf_le_left
    · exact range_pIdemLin_tau1_le_sup F φ
  have hdisj : Disjoint
      (LinearMap.range (pIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (pIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)))
      (LinearMap.range (pIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F))) := by
    apply Disjoint.mono inf_le_right inf_le_right
    exact (isCompl_range_pIdemLin_range_qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)
      (tau2_mul_self F φ)).disjoint
  have h := Submodule.finrank_sup_add_finrank_inf_eq
    (LinearMap.range (pIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
      LinearMap.range (pIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)))
    (LinearMap.range (pIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
      LinearMap.range (qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)))
  have hP1 := finrank_range_pIdemLin_eq_one F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)
    (tau1_mul_self F φ) (tau1_ne_one F φ) (Matrix.SpecialLinearGroup.det_coe (φ (d1SL F)))
  rw [hsup, hdisj.eq_bot, finrank_bot, hP1] at h
  omega

theorem finrank_inf_add_finrank_inf_q1 (φ : AutSL3 F) :
    Module.finrank F ↥(LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (pIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F))) +
      Module.finrank F ↥(LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F))) = 2 := by
  have hsup : (LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (pIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F))) ⊔
      (LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F))) =
      LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) := by
    apply le_antisymm
    · exact sup_le inf_le_left inf_le_left
    · exact range_qIdemLin_tau1_le_sup F φ
  have hdisj : Disjoint
      (LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (pIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)))
      (LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F))) := by
    apply Disjoint.mono inf_le_right inf_le_right
    exact (isCompl_range_pIdemLin_range_qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)
      (tau2_mul_self F φ)).disjoint
  have h := Submodule.finrank_sup_add_finrank_inf_eq
    (LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
      LinearMap.range (pIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)))
    (LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
      LinearMap.range (qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)))
  have hQ1 := finrank_range_qIdemLin_eq_two F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)
    (tau1_mul_self F φ) (tau1_ne_one F φ) (Matrix.SpecialLinearGroup.det_coe (φ (d1SL F)))
  rw [hsup, hdisj.eq_bot, finrank_bot, hQ1] at h
  omega

theorem finrank_inf_q1_q2_le_one (φ : AutSL3 F) :
    Module.finrank F ↥(LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F))) ≤ 1 := by
  have h := Submodule.finrank_mono (inf_q1_q2_le_p3 F φ)
  rwa [finrank_range_pIdemLin_eq_one F (φ (d3SL F) : Matrix (Fin 3) (Fin 3) F)
    (tau3_mul_self F φ) (tau3_ne_one F φ) (Matrix.SpecialLinearGroup.det_coe (φ (d3SL F)))] at h

theorem finrank_inf_q1_p2_le_one (φ : AutSL3 F) :
    Module.finrank F ↥(LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (pIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F))) ≤ 1 := by
  have h := Submodule.finrank_mono (inf_le_right :
    LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (pIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)) ≤
      LinearMap.range (pIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)))
  rwa [finrank_range_pIdemLin_eq_one F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)
    (tau2_mul_self F φ) (tau2_ne_one F φ) (Matrix.SpecialLinearGroup.det_coe (φ (d2SL F)))] at h

theorem finrank_inf_q1_p2_eq_one (φ : AutSL3 F) :
    Module.finrank F ↥(LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (pIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F))) = 1 := by
  have hsum := finrank_inf_add_finrank_inf_q1 F φ
  have hle1 := finrank_inf_q1_p2_le_one F φ
  have hle2 := finrank_inf_q1_q2_le_one F φ
  omega

theorem finrank_inf_q1_q2_eq_one (φ : AutSL3 F) :
    Module.finrank F ↥(LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F))) = 1 := by
  have hsum := finrank_inf_add_finrank_inf_q1 F φ
  have hc := finrank_inf_q1_p2_eq_one F φ
  omega

theorem range_qIdemLin_inf_pIdemLin_eq_p2 (φ : AutSL3 F) :
    LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (pIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)) =
      LinearMap.range (pIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)) := by
  apply Submodule.eq_of_le_of_finrank_eq inf_le_right
  rw [finrank_inf_q1_p2_eq_one F φ,
    finrank_range_pIdemLin_eq_one F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)
      (tau2_mul_self F φ) (tau2_ne_one F φ) (Matrix.SpecialLinearGroup.det_coe (φ (d2SL F)))]

theorem range_pIdemLin_inf_pIdemLin_eq_bot (φ : AutSL3 F) :
    LinearMap.range (pIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (pIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)) = ⊥ := by
  have hP2_eq : LinearMap.range (pIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)) =
      LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (pIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)) :=
    (range_qIdemLin_inf_pIdemLin_eq_p2 F φ).symm
  rw [hP2_eq, ← inf_assoc]
  have hbot : LinearMap.range (pIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
      LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) = ⊥ :=
    (isCompl_range_pIdemLin_range_qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)
      (tau1_mul_self F φ)).disjoint.eq_bot
  rw [hbot, bot_inf_eq]

theorem finrank_inf_p1_p2_eq_zero (φ : AutSL3 F) :
    Module.finrank F ↥(LinearMap.range (pIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (pIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F))) = 0 := by
  rw [range_pIdemLin_inf_pIdemLin_eq_bot F φ, finrank_bot]

theorem finrank_inf_p1_q2_eq_one (φ : AutSL3 F) :
    Module.finrank F ↥(LinearMap.range (pIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F))) = 1 := by
  have hsum := finrank_inf_add_finrank_inf_p1 F φ
  have ha := finrank_inf_p1_p2_eq_zero F φ
  omega

theorem inf_p1_q2_ne_bot (φ : AutSL3 F) :
    LinearMap.range (pIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)) ≠ ⊥ := by
  intro h
  have h1 := finrank_inf_p1_q2_eq_one F φ
  rw [h, finrank_bot] at h1
  exact absurd h1 (by norm_num)

theorem inf_q1_p2_ne_bot (φ : AutSL3 F) :
    LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (pIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)) ≠ ⊥ := by
  intro h
  have h1 := finrank_inf_q1_p2_eq_one F φ
  rw [h, finrank_bot] at h1
  exact absurd h1 (by norm_num)

theorem inf_q1_q2_ne_bot (φ : AutSL3 F) :
    LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)) ≠ ⊥ := by
  intro h
  have h1 := finrank_inf_q1_q2_eq_one F φ
  rw [h, finrank_bot] at h1
  exact absurd h1 (by norm_num)

/-! ### Extracting basis vectors `v1, v2, v3` and checking they are independent

`v1` spans `P1 ⊓ Q2` (`τ1 = +1`, `τ2 = -1`), `v2` spans `Q1 ⊓ P2`, `v3` spans `Q1 ⊓ Q2` —
each is exactly 1-dimensional by the previous section, hence nonzero and unique up to
scalar. `linearIndependent_v1_v2_v3` checks that any vanishing combination of the three
forces all three coefficients to vanish (using that `τ1`, `τ2` act by different sign
patterns on each `vᵢ`). -/

theorem exists_v1 (φ : AutSL3 F) :
    ∃ v : Fin 3 → F, v ∈ LinearMap.range (pIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)) ∧ v ≠ 0 :=
  Submodule.exists_mem_ne_zero_of_ne_bot (inf_p1_q2_ne_bot F φ)

theorem exists_v2 (φ : AutSL3 F) :
    ∃ v : Fin 3 → F, v ∈ LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (pIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)) ∧ v ≠ 0 :=
  Submodule.exists_mem_ne_zero_of_ne_bot (inf_q1_p2_ne_bot F φ)

theorem exists_v3 (φ : AutSL3 F) :
    ∃ v : Fin 3 → F, v ∈ LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)) ∧ v ≠ 0 :=
  Submodule.exists_mem_ne_zero_of_ne_bot (inf_q1_q2_ne_bot F φ)

theorem linearIndependent_v1_v2_v3 (φ : AutSL3 F)
    {v1 v2 v3 : Fin 3 → F}
    (hv1 : v1 ∈ LinearMap.range (pIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)))
    (hv2 : v2 ∈ LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (pIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)))
    (hv3 : v3 ∈ LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)))
    (hv1' : v1 ≠ 0) (hv2' : v2 ≠ 0) (hv3' : v3 ≠ 0)
    (a b c : F) (h : a • v1 + b • v2 + c • v3 = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 := by
  have e1_1 : tauLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F) v1 = v1 :=
    mem_range_pIdemLin_iff_eigen F _ (tau1_mul_self F φ) v1 hv1.1
  have e1_2 : tauLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F) v1 = -v1 :=
    mem_range_qIdemLin_iff_eigen F _ (tau2_mul_self F φ) v1 hv1.2
  have e2_1 : tauLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F) v2 = -v2 :=
    mem_range_qIdemLin_iff_eigen F _ (tau1_mul_self F φ) v2 hv2.1
  have e2_2 : tauLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F) v2 = v2 :=
    mem_range_pIdemLin_iff_eigen F _ (tau2_mul_self F φ) v2 hv2.2
  have e3_1 : tauLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F) v3 = -v3 :=
    mem_range_qIdemLin_iff_eigen F _ (tau1_mul_self F φ) v3 hv3.1
  have e3_2 : tauLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F) v3 = -v3 :=
    mem_range_qIdemLin_iff_eigen F _ (tau2_mul_self F φ) v3 hv3.2
  have h1 : a • v1 + -(b • v2) + -(c • v3) = 0 := by
    have hh := congrArg (tauLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) h
    rw [map_zero, map_add, map_add, map_smul, map_smul, map_smul, e1_1, e2_1, e3_1,
      smul_neg, smul_neg] at hh
    exact hh
  have hadd : a • v1 + a • v1 = 0 := by
    have heq : (a • v1 + b • v2 + c • v3) + (a • v1 + -(b • v2) + -(c • v3)) =
        a • v1 + a • v1 := by abel
    rw [h, h1] at heq
    simpa using heq.symm
  have ha : a = 0 := by
    have h2 : (2 : F) • (a • v1) = 0 := by rw [two_smul]; exact hadd
    rw [smul_smul] at h2
    rcases smul_eq_zero.mp h2 with h2a | hv
    · rcases mul_eq_zero.mp h2a with h20 | ha0
      · exact absurd h20 (Invertible.ne_zero (2 : F))
      · exact ha0
    · exact absurd hv hv1'
  have hbc : b • v2 + c • v3 = 0 := by
    rw [ha] at h
    simpa using h
  have h2 : b • v2 + -(c • v3) = 0 := by
    have hh := congrArg (tauLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)) hbc
    rw [map_zero, map_add, map_smul, map_smul, e2_2, e3_2, smul_neg] at hh
    exact hh
  have hbadd : b • v2 + b • v2 = 0 := by
    have heq : (b • v2 + c • v3) + (b • v2 + -(c • v3)) = b • v2 + b • v2 := by abel
    rw [hbc, h2] at heq
    simpa using heq.symm
  have hb : b = 0 := by
    have h2' : (2 : F) • (b • v2) = 0 := by rw [two_smul]; exact hbadd
    rw [smul_smul] at h2'
    rcases smul_eq_zero.mp h2' with h2b | hv
    · rcases mul_eq_zero.mp h2b with h20 | hb0
      · exact absurd h20 (Invertible.ne_zero (2 : F))
      · exact hb0
    · exact absurd hv hv2'
  have hc : c = 0 := by
    rw [hb] at hbc
    simp only [zero_smul, zero_add] at hbc
    rcases smul_eq_zero.mp hbc with hc0 | hv
    · exact hc0
    · exact absurd hv hv3'
  exact ⟨ha, hb, hc⟩

theorem linearIndependent_fin3 (φ : AutSL3 F)
    (v1 v2 v3 : Fin 3 → F)
    (hv1 : v1 ∈ LinearMap.range (pIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)))
    (hv2 : v2 ∈ LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (pIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)))
    (hv3 : v3 ∈ LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)))
    (hv1' : v1 ≠ 0) (hv2' : v2 ≠ 0) (hv3' : v3 ≠ 0) :
    LinearIndependent F ![v1, v2, v3] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg i
  have key := linearIndependent_v1_v2_v3 F φ hv1 hv2 hv3 hv1' hv2' hv3' (g 0) (g 1) (g 2) (by
    have : ∑ j : Fin 3, g j • (![v1, v2, v3] j) = g 0 • v1 + g 1 • v2 + g 2 • v3 := by
      simp [Fin.sum_univ_three]
    rw [← this]; exact hg)
  fin_cases i
  · exact key.1
  · exact key.2.1
  · exact key.2.2

noncomputable def basisV123 (φ : AutSL3 F)
    (v1 v2 v3 : Fin 3 → F)
    (hv1 : v1 ∈ LinearMap.range (pIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)))
    (hv2 : v2 ∈ LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (pIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)))
    (hv3 : v3 ∈ LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)))
    (hv1' : v1 ≠ 0) (hv2' : v2 ≠ 0) (hv3' : v3 ≠ 0) :
    Module.Basis (Fin 3) F (Fin 3 → F) :=
  basisOfLinearIndependentOfCardEqFinrank
    (linearIndependent_fin3 F φ v1 v2 v3 hv1 hv2 hv3 hv1' hv2' hv3')
    (by simp)

/-! ### Building the change-of-basis matrix `g`

`gMatrix v1 v2 v3` is the matrix whose columns are `v1, v2, v3`. We check it sends the
standard basis vectors to `v1, v2, v3` (`gMatrix_mulVec_e1/e2/e3`), that it is injective
(hence invertible, via `linearIndependent_v1_v2_v3`), and finally that
`τᵢ · g = g · dᵢ` for `i = 1, 2, 3` by comparing both sides column by column
(`tau1_mul_gMatrix_eq`, `tau2_mul_gMatrix_eq`, and `g_inv_mul_tau3_mul_g` via
`τ3 = τ1 τ2`, `d3 = d1 d2`). -/

noncomputable def gMatrix (v1 v2 v3 : Fin 3 → F) : Matrix (Fin 3) (Fin 3) F :=
  fun i j => ![v1, v2, v3] j i

omit [Invertible (2 : F)] in
theorem gMatrix_mulVec_e1 (v1 v2 v3 : Fin 3 → F) :
    (gMatrix F v1 v2 v3).mulVec (e1 F) = v1 := by
  ext i
  simp [gMatrix, Matrix.mulVec, e1]

omit [Invertible (2 : F)] in
theorem gMatrix_mulVec_e2 (v1 v2 v3 : Fin 3 → F) :
    (gMatrix F v1 v2 v3).mulVec (e2 F) = v2 := by
  ext i
  simp [gMatrix, Matrix.mulVec, e2]

omit [Invertible (2 : F)] in
theorem gMatrix_mulVec_e3 (v1 v2 v3 : Fin 3 → F) :
    (gMatrix F v1 v2 v3).mulVec (e3 F) = v3 := by
  ext i
  simp [gMatrix, Matrix.mulVec, e3]


omit [Invertible (2 : F)] in
theorem gMatrix_mulVec_general (v1 v2 v3 : Fin 3 → F) (x : Fin 3 → F) :
    (gMatrix F v1 v2 v3).mulVec x = x 0 • v1 + x 1 • v2 + x 2 • v3 := by
  funext i
  show ∑ j, gMatrix F v1 v2 v3 i j * x j = (x 0 • v1 + x 1 • v2 + x 2 • v3) i
  rw [Fin.sum_univ_three]
  simp [gMatrix]
  ring

theorem gMatrix_injective (φ : AutSL3 F)
    (v1 v2 v3 : Fin 3 → F)
    (hv1 : v1 ∈ LinearMap.range (pIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)))
    (hv2 : v2 ∈ LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (pIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)))
    (hv3 : v3 ∈ LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)))
    (hv1' : v1 ≠ 0) (hv2' : v2 ≠ 0) (hv3' : v3 ≠ 0) :
    Function.Injective (gMatrix F v1 v2 v3).mulVec := by
  intro x y hxy
  rw [gMatrix_mulVec_general, gMatrix_mulVec_general] at hxy
  have heq : (x 0 - y 0) • v1 + (x 1 - y 1) • v2 + (x 2 - y 2) • v3 = 0 := by
    rw [sub_smul, sub_smul, sub_smul]
    rw [show x 0 • v1 - y 0 • v1 + (x 1 • v2 - y 1 • v2) + (x 2 • v3 - y 2 • v3) =
      (x 0 • v1 + x 1 • v2 + x 2 • v3) - (y 0 • v1 + y 1 • v2 + y 2 • v3) from by abel]
    rw [hxy, sub_self]
  have key := linearIndependent_v1_v2_v3 F φ hv1 hv2 hv3 hv1' hv2' hv3'
    (x 0 - y 0) (x 1 - y 1) (x 2 - y 2) heq
  funext j
  fin_cases j
  · exact sub_eq_zero.mp key.1
  · exact sub_eq_zero.mp key.2.1
  · exact sub_eq_zero.mp key.2.2

omit [Invertible (2 : F)] in
theorem gMatrix_det_ne_zero (v1 v2 v3 : Fin 3 → F)
    (hinj : Function.Injective (gMatrix F v1 v2 v3).mulVec) :
    (gMatrix F v1 v2 v3).det ≠ 0 := by
  intro hdet
  obtain ⟨v, hv_ne, hv_zero⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  apply hv_ne
  have h0 : (gMatrix F v1 v2 v3).mulVec 0 = 0 := Matrix.mulVec_zero _
  exact hinj (hv_zero.trans h0.symm)

omit [Invertible (2 : F)] in
theorem gMatrix_isUnit (v1 v2 v3 : Fin 3 → F)
    (hinj : Function.Injective (gMatrix F v1 v2 v3).mulVec) :
    IsUnit (gMatrix F v1 v2 v3) :=
  (Matrix.isUnit_iff_isUnit_det _).mpr (Ne.isUnit (gMatrix_det_ne_zero F v1 v2 v3 hinj))

omit [Invertible (2 : F)] in
theorem tauLin_apply_eq_mulVec (τ : Matrix (Fin 3) (Fin 3) F) (x : Fin 3 → F) :
    tauLin F τ x = τ.mulVec x := by
  unfold tauLin
  rw [Matrix.toLinAlgEquiv'_apply]

omit [Invertible (2 : F)] in
theorem d1_mulVec_e1 : (d1 F).mulVec (e1 F) = e1 F := by
  funext i
  show ∑ j, (d1 F) i j * (e1 F) j = (e1 F) i
  rw [Fin.sum_univ_three]
  fin_cases i <;> simp [d1, e1, Matrix.diagonal]

omit [Invertible (2 : F)] in
theorem d1_mulVec_e2 : (d1 F).mulVec (e2 F) = -(e2 F) := by
  funext i
  show ∑ j, (d1 F) i j * (e2 F) j = -(e2 F) i
  rw [Fin.sum_univ_three]
  fin_cases i <;> simp [d1, e2, Matrix.diagonal]

omit [Invertible (2 : F)] in
theorem d1_mulVec_e3 : (d1 F).mulVec (e3 F) = -(e3 F) := by
  funext i
  show ∑ j, (d1 F) i j * (e3 F) j = -(e3 F) i
  rw [Fin.sum_univ_three]
  fin_cases i <;> simp [d1, e3, Matrix.diagonal]

omit [Invertible (2 : F)] in
theorem d2_mulVec_e1 : (d2 F).mulVec (e1 F) = -(e1 F) := by
  funext i
  show ∑ j, (d2 F) i j * (e1 F) j = -(e1 F) i
  rw [Fin.sum_univ_three]
  fin_cases i <;> simp [d2, e1, Matrix.diagonal]

omit [Invertible (2 : F)] in
theorem d2_mulVec_e2 : (d2 F).mulVec (e2 F) = e2 F := by
  funext i
  show ∑ j, (d2 F) i j * (e2 F) j = (e2 F) i
  rw [Fin.sum_univ_three]
  fin_cases i <;> simp [d2, e2, Matrix.diagonal]

omit [Invertible (2 : F)] in
theorem d2_mulVec_e3 : (d2 F).mulVec (e3 F) = -(e3 F) := by
  funext i
  show ∑ j, (d2 F) i j * (e3 F) j = -(e3 F) i
  rw [Fin.sum_univ_three]
  fin_cases i <;> simp [d2, e3, Matrix.diagonal]

omit [Invertible (2 : F)] in
theorem mulVec_e1_eq_col0 (M : Matrix (Fin 3) (Fin 3) F) :
    M.mulVec (e1 F) = fun i => M i 0 := by
  funext i
  show ∑ j, M i j * (e1 F) j = M i 0
  rw [Fin.sum_univ_three]
  simp [e1]

omit [Invertible (2 : F)] in
theorem mulVec_e2_eq_col1 (M : Matrix (Fin 3) (Fin 3) F) :
    M.mulVec (e2 F) = fun i => M i 1 := by
  funext i
  show ∑ j, M i j * (e2 F) j = M i 1
  rw [Fin.sum_univ_three]
  simp [e2]

omit [Invertible (2 : F)] in
theorem mulVec_e3_eq_col2 (M : Matrix (Fin 3) (Fin 3) F) :
    M.mulVec (e3 F) = fun i => M i 2 := by
  funext i
  show ∑ j, M i j * (e3 F) j = M i 2
  rw [Fin.sum_univ_three]
  simp [e3]

omit [Invertible (2 : F)] in
theorem matrix_ext_of_mulVec_e (M N : Matrix (Fin 3) (Fin 3) F)
    (h1 : M.mulVec (e1 F) = N.mulVec (e1 F))
    (h2 : M.mulVec (e2 F) = N.mulVec (e2 F))
    (h3 : M.mulVec (e3 F) = N.mulVec (e3 F)) : M = N := by
  rw [mulVec_e1_eq_col0, mulVec_e1_eq_col0] at h1
  rw [mulVec_e2_eq_col1, mulVec_e2_eq_col1] at h2
  rw [mulVec_e3_eq_col2, mulVec_e3_eq_col2] at h3
  ext i j
  fin_cases j
  · exact congrFun h1 i
  · exact congrFun h2 i
  · exact congrFun h3 i

theorem tau1_mul_gMatrix_eq (φ : AutSL3 F)
    (v1 v2 v3 : Fin 3 → F)
    (hv1 : v1 ∈ LinearMap.range (pIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)))
    (hv2 : v2 ∈ LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (pIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)))
    (hv3 : v3 ∈ LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F))) :
    (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F) * gMatrix F v1 v2 v3 =
      gMatrix F v1 v2 v3 * d1 F := by
  apply matrix_ext_of_mulVec_e
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, d1_mulVec_e1, gMatrix_mulVec_e1,
      ← tauLin_apply_eq_mulVec]
    exact mem_range_pIdemLin_iff_eigen F _ (tau1_mul_self F φ) v1 hv1.1
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, d1_mulVec_e2, Matrix.mulVec_neg,
      gMatrix_mulVec_e2, ← tauLin_apply_eq_mulVec]
    exact mem_range_qIdemLin_iff_eigen F _ (tau1_mul_self F φ) v2 hv2.1
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, d1_mulVec_e3, Matrix.mulVec_neg,
      gMatrix_mulVec_e3, ← tauLin_apply_eq_mulVec]
    exact mem_range_qIdemLin_iff_eigen F _ (tau1_mul_self F φ) v3 hv3.1

theorem tau2_mul_gMatrix_eq (φ : AutSL3 F)
    (v1 v2 v3 : Fin 3 → F)
    (hv1 : v1 ∈ LinearMap.range (pIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)))
    (hv2 : v2 ∈ LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (pIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)))
    (hv3 : v3 ∈ LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F))) :
    (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F) * gMatrix F v1 v2 v3 =
      gMatrix F v1 v2 v3 * d2 F := by
  apply matrix_ext_of_mulVec_e
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, d2_mulVec_e1, Matrix.mulVec_neg,
      gMatrix_mulVec_e1, ← tauLin_apply_eq_mulVec]
    exact mem_range_qIdemLin_iff_eigen F _ (tau2_mul_self F φ) v1 hv1.2
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, d2_mulVec_e2, gMatrix_mulVec_e2,
      ← tauLin_apply_eq_mulVec]
    exact mem_range_pIdemLin_iff_eigen F _ (tau2_mul_self F φ) v2 hv2.2
  · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, d2_mulVec_e3, Matrix.mulVec_neg,
      gMatrix_mulVec_e3, ← tauLin_apply_eq_mulVec]
    exact mem_range_qIdemLin_iff_eigen F _ (tau2_mul_self F φ) v3 hv3.2

theorem g_inv_mul_tau1_mul_g (φ : AutSL3 F)
    (v1 v2 v3 : Fin 3 → F)
    (hv1 : v1 ∈ LinearMap.range (pIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)))
    (hv2 : v2 ∈ LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (pIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)))
    (hv3 : v3 ∈ LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)))
    (hinj : Function.Injective (gMatrix F v1 v2 v3).mulVec) :
    (gMatrix F v1 v2 v3)⁻¹ * (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F) * gMatrix F v1 v2 v3 =
      d1 F := by
  have heq := tau1_mul_gMatrix_eq F φ v1 v2 v3 hv1 hv2 hv3
  have hnonsing : (gMatrix F v1 v2 v3)⁻¹ * gMatrix F v1 v2 v3 = 1 :=
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp (gMatrix_isUnit F v1 v2 v3 hinj))
  rw [mul_assoc, heq, ← mul_assoc, hnonsing, one_mul]

theorem g_inv_mul_tau2_mul_g (φ : AutSL3 F)
    (v1 v2 v3 : Fin 3 → F)
    (hv1 : v1 ∈ LinearMap.range (pIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)))
    (hv2 : v2 ∈ LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (pIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)))
    (hv3 : v3 ∈ LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)))
    (hinj : Function.Injective (gMatrix F v1 v2 v3).mulVec) :
    (gMatrix F v1 v2 v3)⁻¹ * (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F) * gMatrix F v1 v2 v3 =
      d2 F := by
  have heq := tau2_mul_gMatrix_eq F φ v1 v2 v3 hv1 hv2 hv3
  have hnonsing : (gMatrix F v1 v2 v3)⁻¹ * gMatrix F v1 v2 v3 = 1 :=
    Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).mp (gMatrix_isUnit F v1 v2 v3 hinj))
  rw [mul_assoc, heq, ← mul_assoc, hnonsing, one_mul]

omit [Invertible (2 : F)] in
theorem conj_mul_eq (g A B : Matrix (Fin 3) (Fin 3) F) (hg_mul : g * g⁻¹ = 1) :
    g⁻¹ * (A * B) * g = (g⁻¹ * A * g) * (g⁻¹ * B * g) := by
  have step : (g⁻¹ * A * g) * (g⁻¹ * B * g) = g⁻¹ * A * (g * g⁻¹) * B * g := by
    simp only [mul_assoc]
  rw [step, hg_mul, mul_one]
  simp only [mul_assoc]

theorem g_inv_mul_tau3_mul_g (φ : AutSL3 F)
    (v1 v2 v3 : Fin 3 → F)
    (hv1 : v1 ∈ LinearMap.range (pIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)))
    (hv2 : v2 ∈ LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (pIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)))
    (hv3 : v3 ∈ LinearMap.range (qIdemLin F (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F)) ⊓
        LinearMap.range (qIdemLin F (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F)))
    (hinj : Function.Injective (gMatrix F v1 v2 v3).mulVec) :
    (gMatrix F v1 v2 v3)⁻¹ * (φ (d3SL F) : Matrix (Fin 3) (Fin 3) F) * gMatrix F v1 v2 v3 =
      d3 F := by
  have hg_mul : gMatrix F v1 v2 v3 * (gMatrix F v1 v2 v3)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).mp (gMatrix_isUnit F v1 v2 v3 hinj))
  have h3 : (φ (d3SL F) : Matrix (Fin 3) (Fin 3) F) =
      (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F) * (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F) :=
    (tau1_mul_tau2_eq_tau3 F φ).symm
  have hd3 : d3 F = d1 F * d2 F := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [d1, d2, d3, Matrix.diagonal, Matrix.mul_apply, Fin.sum_univ_three]
  rw [h3, hd3, conj_mul_eq F (gMatrix F v1 v2 v3) _ _ hg_mul,
    g_inv_mul_tau1_mul_g F φ v1 v2 v3 hv1 hv2 hv3 hinj,
    g_inv_mul_tau2_mul_g F φ v1 v2 v3 hv1 hv2 hv3 hinj]


/-! ### Final assembly

Package `(gMatrix v1 v2 v3)⁻¹` directly as a `Units` (val/inv given explicitly, so the
two coercions `↑g` and `↑g⁻¹` are the relevant matrices *by definition*, no extra
rewriting needed), and discharge the three conjugation identities via
`g_inv_mul_tauᵢ_mul_g`. -/

theorem diag_preserved_after_change_of_basis
    (φ : AutSL3 F) :
    ∃ g : GL3 F,
      innerAutSL3byGL3 F g (φ (d1SL F)) = d1SL F ∧
      innerAutSL3byGL3 F g (φ (d2SL F)) = d2SL F ∧
      innerAutSL3byGL3 F g (φ (d3SL F)) = d3SL F := by
  obtain ⟨v1, hv1, hv1'⟩ := exists_v1 F φ
  obtain ⟨v2, hv2, hv2'⟩ := exists_v2 F φ
  obtain ⟨v3, hv3, hv3'⟩ := exists_v3 F φ
  have hinj := gMatrix_injective F φ v1 v2 v3 hv1 hv2 hv3 hv1' hv2' hv3'
  have hdetu : IsUnit (gMatrix F v1 v2 v3).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (gMatrix_isUnit F v1 v2 v3 hinj)
  have hvi : (gMatrix F v1 v2 v3)⁻¹ * gMatrix F v1 v2 v3 = 1 :=
    Matrix.nonsing_inv_mul _ hdetu
  have hiv : gMatrix F v1 v2 v3 * (gMatrix F v1 v2 v3)⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ hdetu
  refine ⟨⟨(gMatrix F v1 v2 v3)⁻¹, gMatrix F v1 v2 v3, hvi, hiv⟩, ?_, ?_, ?_⟩
  · apply Subtype.ext
    show (gMatrix F v1 v2 v3)⁻¹ * (φ (d1SL F) : Matrix (Fin 3) (Fin 3) F) *
        gMatrix F v1 v2 v3 = d1 F
    exact g_inv_mul_tau1_mul_g F φ v1 v2 v3 hv1 hv2 hv3 hinj
  · apply Subtype.ext
    show (gMatrix F v1 v2 v3)⁻¹ * (φ (d2SL F) : Matrix (Fin 3) (Fin 3) F) *
        gMatrix F v1 v2 v3 = d2 F
    exact g_inv_mul_tau2_mul_g F φ v1 v2 v3 hv1 hv2 hv3 hinj
  · apply Subtype.ext
    show (gMatrix F v1 v2 v3)⁻¹ * (φ (d3SL F) : Matrix (Fin 3) (Fin 3) F) *
        gMatrix F v1 v2 v3 = d3 F
    exact g_inv_mul_tau3_mul_g F φ v1 v2 v3 hv1 hv2 hv3 hinj


def w1 : Matrix (Fin 3) (Fin 3) (R) :=
    !![0, -1, 0;
     1, 0, 0;
     0, 0, 1]

def w2 : Matrix (Fin 3) (Fin 3) (R) :=
    !![1, 0, 0;
     0, 0, 1;
     0, -1, 0]

def w1SL : SL3 R :=
  ⟨w1 R, by
    simp [w1, Matrix.det_fin_three]
  ⟩

def w2SL : SL3 R :=
  ⟨w2 R, by
    simp [w2, Matrix.det_fin_three]
  ⟩

theorem w_preserved
    (φ : AutSL3 F) :
    ∃ g : GL3 F,
      innerAutSL3byGL3 F g (φ (d1SL F)) = d1SL F ∧
      innerAutSL3byGL3 F g (φ (d2SL F)) = d2SL F ∧
      innerAutSL3byGL3 F g (φ (d3SL F)) = d3SL F ∧
      innerAutSL3byGL3 F g (φ (w1SL F)) = w1SL F ∧
      innerAutSL3byGL3 F g (φ (w2SL F)) = w2SL F := by
  sorry



def x12 : Matrix (Fin 3) (Fin 3) (R) :=
    !![1, 1, 0;
     0, 1, 0;
     0, 0, 1]

def x12SL : SL3 R :=
  ⟨x12 R, by
    simp [x12, Matrix.det_fin_three]
  ⟩



def graphChoiceSL3 (ε : Bool) : AutSL3 R :=
  if ε then invTransposeAutSL3 R else (1 : AutSL3 R)


theorem x12_preserved (φ : AutSL3 (F)) : ∃ (g : GL3 F) (ε : Bool),
      graphChoiceSL3 F ε (innerAutSL3byGL3 F g (φ (d1SL F))) = d1SL F ∧
      graphChoiceSL3 F ε (innerAutSL3byGL3 F g (φ (d2SL F))) = d2SL F ∧
      graphChoiceSL3 F ε (innerAutSL3byGL3 F g (φ (d3SL F))) = d3SL F ∧
      graphChoiceSL3 F ε (innerAutSL3byGL3 F g (φ (w1SL F))) = w1SL F ∧
      graphChoiceSL3 F ε (innerAutSL3byGL3 F g (φ (w2SL F))) = w2SL F ∧
      graphChoiceSL3 F ε (innerAutSL3byGL3 F g (φ (x12SL F))) = x12SL F := by
  sorry


def IsTransvectionSL3 (x : SL3 F) : Prop :=
  ∃ i j : Fin 3, ∃ c : F,
    i ≠ j ∧
    (x : Matrix (Fin 3) (Fin 3) F) =
      Matrix.transvection i j c


theorem field_class
    (φ : AutSL3 F) :
    ∃ (σ : F ≃+* F) (ε : Bool) (g : GL (Fin 3) F),
      ∀ (x : SL3 F),
        φ x =
            ringAutSL3 F σ ((graphChoiceSL3 F ε) (innerAutSL3byGL3 F g x))
             := by
  sorry

end FieldAutomorpisms
