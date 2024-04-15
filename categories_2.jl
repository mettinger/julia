using Metatheory
using Metatheory.EGraphs
using Metatheory.Library

using Debugger

mutable struct Category
    src::Dict
    target::Dict
    relations
end

function checkId(morphism)::Bool
    morphism = repr(morphism)
    if occursin("id", morphism)
        return true
    else
        return false
    end
end

identity = @theory f g begin
    comp(g::checkId, f) --> f 
    comp(f, g::checkId) --> f
end

function addIdentityMorphism(src, target)
    objects = union(Set(values(src)), Set(values(target)))
    for thisObject in objects
        src["id" * thisObject] = thisObject
        target["id" * thisObject] = thisObject
    end
    return src,target
end

# Initialize a category and test it 
function categoryInit(src::Dict, target::Dict, relations)

    src, target = addIdentityMorphism(src, target)

    cat = Category(src, target, relations);
    if checkComposability(cat, true)
        if checkComposition(cat, true)
            if checkAssociativity(cat, true)
                return cat
            end
        end
    end
end;

#Check that all the composables defined by equations have matching targets and sources.
function checkComposability(c::Category, debug::Bool=false)

    for thisEquality in c.relations
        if !occursin("checkId", string(thisEquality.left))
            second, first = thisEquality.left.args 
            if typeof(second) == PatTerm 
                second = (second.args[1], second.args[2])
                first = (first.args[1], first.args[2])
            end
            
            if c.src[second] != c.target[first]
                if debug
                    println("composability violation")
                    println(first,second)
                    println(" ")
                end
                return false
            end
        end
    end
    return true
end

# Compose arrows j and i and then simplify to a name
function simplifyComposition(i::String, j::String, relations) :: String

    relations = relations ∪  identity

    expression = Meta.parse("comp(\"$j\", \"$i\")") 
    g = EGraph(expression)
    saturate!(g, relations)
    simplified = extract!(g, astsize)
    return simplified
end

# Check that category c satisfies associativity by brute force
function checkAssociativity(c::Category, debug::Bool = false) :: Bool
    morphisms = keys(c.src)
 
    for i in morphisms
        for j in morphisms
            for k in morphisms
                if (c.target[i] == c.src[j]) && (c.target[j] == c.src[k])
                    leftAssocLeft = simplifyComposition(i, j, c.relations)
                    leftAssoc = simplifyComposition(leftAssocLeft, k, c.relations)
                    rightAssocRight = simplifyComposition(j, k, c.relations)
                    rightAssoc = simplifyComposition(i, rightAssocRight, c.relations)
                    if leftAssoc != rightAssoc
                        if debug
                            print("associativity violation: ")
                            println(k,j,i)
                            println(leftAssocLeft)
                            println(leftAssoc)
                            println(rightAssocRight)
                            println(rightAssoc)
                            println(" ")
                        end

                        return false
                    end
                end
            end
        end
    end

    return true
end;

#Check that the composition of any two arrows with matching sources and targets has a name by brute force
function checkComposition(c::Category, debug::Bool=false) :: Bool
    
    morphisms = [morph for morph in keys(c.src) if !occursin("id", morph)]
    leftSides = Set([string(thisEquality.left) for thisEquality in c.relations])

    for i in morphisms
        for j in morphisms
            if c.target[i] == c.src[j]
                thisComposition = "comp(\"$j\", \"$i\")"
                if !in(thisComposition, leftSides) # check if composition is a left side of some equation
                    if debug
                        println("missing composition name: ")
                        println(i,j)
                        println(" ")
                    end
                    return false
                end
            end
        end
    end
    return true
end;

#=
function productCategory(c::Category, d::Category)
    src = srcProduct(c, d)
    target = targetProduct(c, d)
    relations = relationsProduct(c, d)
    productCat = categoryInit(src, target, relations)
    return productCat
end;

function srcProduct(c::Category, d::Category)
    srcKeys = [(i,j) for i in keys(c.src) for j in keys(d.src)]
    srcValues = [(i,j) for i in values(c.src) for j in values(d.src)]
    return Dict(zip(srcKeys, srcValues))
end

function targetProduct(c::Category, d::Category)
    targetKeys = [(i,j) for i in keys(c.target) for j in keys(d.target)]
    targetValues = [(i,j) for i in values(c.target) for j in values(d.target)]
    return Dict(zip(targetKeys, targetValues))
end

function relationsProduct(c::Category, d::Category)
    relations = Vector{EqualityRule}([])
    for cRelation in c.relations
        for dRelation in d.relations
            temp = 5
            thisRelation = @rule ($(cRelation.left.args[1]), $(dRelation.left.args[1])) ∘ ($(cRelation.left.args[2]), $(dRelation.left.args[2]))  == ($(cRelation.right), $(dRelation.right))
            push!(relations, thisRelation)
        end
    end
    return relations
end;
=#

src = Dict("f" => "0", "g" => "1", "h" => "2", "i" => "0", "k" => "1", "m" => "0", "n" => "0")
target = Dict("f" => "1", "g" => "2", "h" => "3", "i" => "2", "k" => "3", :"m" => "3", "n" => "3")

relations = @theory begin
    comp("g", "f") --> "i"
    comp("h", "g") --> "k"
    comp("h", "i") --> "m"
    comp("k", "f") --> "m" 
end


#temp = simplifyComposition("f", "id1", relations)
cat1 = categoryInit(src, target, relations);
cat2 = categoryInit(src, target, relations);

cat1CrossCat2 = productCategory(cat1, cat2)

