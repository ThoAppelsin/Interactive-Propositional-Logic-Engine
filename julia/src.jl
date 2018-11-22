Formula = Union{Atom, Neg, And, Or, Imp}

Atom = AbstractString

struct Neg
	ϕ::Formula
end

struct And
	ϕ₁::Formula
	ϕ₂::Formula
end

struct Or
	ϕ₁::Formula
	ϕ₂::Formula
end

struct Imp
	ϕ₁::Formula
	ϕ₂::Formula
end

struct Sequent
	premises::Array{Formula}
	conclusion::Formula
end

@enum Assoc LeftAssoc RightAssoc

PARENS = ["()", "[]"]
ATOM = r"^[A-Za-z][0-9]*$"
NEG = (Neg, ["¬", "!", "-"])
AND = (And, ["∧", "&", "*", "×"])
OR  = (Or,  ["∧", "|", "+"])
IMP = (Imp, ["→", "->"])

function balanced_parens(ϕ, parens)
	c = 0
	for x ∈ ϕ
		if x == parens[1]
			c += 1
		elseif x == parens[2]
			c -= 1
			if c < 0
				return false
			end
		end
	end
	return c == 0
end

balanced_parens(ϕ) = all(balanced_parens(ϕ, parens) for parens ∈ PARENS)

function parse_unary(ϕ, OP)
	Op, ops = OP
	for op ∈ ops
		if startswith(ϕ, op)
			return Op(parse_formula(a[length(op)+1:end]))
		end
	end
end

function parse_binary(ϕ, OP, assoc)
	Op, ops = OP
	for op ∈ ops
		if op ∈ ϕ
			splits = split(ϕ, op)
			e_range = (assoc == LeftAssoc ? reverse : identity)(1:length(splits)-1)
			for e ∈ e_range
				ϕ₁ = join(splits[1:e], op)
				ϕ₂ = join(splits[e+1:end], op)
				if balanced_parens(ϕ₁) && balanced_parens(ϕ₂)
					return Op(parse_formula(ϕ₁), parse_formula(ϕ₂))
				end
			end
		end
	end
end

is_atomic(ϕ) = match(ATOM, ϕ) == ϕ
parse_neg(ϕ) = parse_unary(ϕ, NEG)
parse_and(ϕ) = parse_binary(ϕ, AND, LeftAssoc)
parse_or(ϕ)  = parse_binary(ϕ, OR,  LeftAssoc)
parse_imp(ϕ) = parse_binary(ϕ, IMP, RightAssoc)

function converge(subject, functions)
	while true
		subject_old = subject
		for f ∈ functions
			subject = f(subject)
		end
		if subject_old == subject
			return subject
		end
	end
end

strip_parens(ϕ, parens) = ϕ[[1, end]] == parens ? ϕ[2:end-1] : ϕ
strip_parens(ϕ) = converge(ϕ, [strip_parens(ϕ, parens) for PARENS])
strip_formula(ϕ) = converge(ϕ, [strip, strip_parens])

function parse_formula(ϕ)
	ϕ = strip_formula(ϕ)
	for p in [parse_imp, parse_or, parse_and, parse_neg]
		if (ϕ⁺ = p(ϕ)) ≠ nothing
			return ϕ⁺
		end
	end
	if is_atomic(ϕ)
		return ϕ
	else
		println("Either we parsed it wrong or you supplied a malformed formula: >$ϕ<")
	end
end
