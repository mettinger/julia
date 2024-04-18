using Metatheory
using Metatheory.EGraphs
using Metatheory.Library

using Debugger

mutable struct Category
    src::Dict
    target::Dict
    relations
    identityRelations
end

function addIdentityMorphisms(src, target)
    objects = union(Set(values(src)), Set(values(target)))
    morphisms = keys(src)
    identityRelations = Vector{EqualityRule}([])

    # define source and targets for identities
    for thisObject in objects
        thisObject = string(thisObject)
        thisIdMorphism = "id" * thisObject
        src[thisIdMorphism] = thisObject
        target[thisIdMorphism] = thisObject

        # add rewrite rules for identity morphisms
        for thisMorphism in morphisms
            if src[thisMorphism] == thisObject
                thisRelation = @rule comp($thisMorphism, $thisIdMorphism) == $thisMorphism
                push!(identityRelations, thisRelation)
            end

            if target[thisMorphism] == thisObject
                thisRelation = @rule comp($thisIdMorphism, $thisMorphism) == $thisMorphism
                push!(identityRelations, thisRelation)
            end
        end
    end
    return src,target, identityRelations
end

# Compose arrows j and i and then simplify to a name
function simplifyComposition(i::String, j::String, relations, identityRelations) :: String

    relations = relations ∪  identityRelations

    expression = Meta.parse("comp(\"$j\", \"$i\")") 
    g = EGraph(expression)
    saturate!(g, relations)
    simplified = extract!(g, astsize)
    return simplified
end

# Initialize a category and test it 
function categoryInit(src::Dict, target::Dict, relations, identityRelations; addIdentity::Bool)

    if addIdentity
        src, target, identityRelations = addIdentityMorphisms(src, target)
    end

    cat = Category(src, target, relations, identityRelations);
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
        if !occursin("~", string(thisEquality.left))
            second, first = thisEquality.left.args 
            second = string(second)
            first = string(first)
            
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

#Check that the composition of any two arrows with matching sources and targets has a name by brute force
function checkComposition(c::Category, debug::Bool=false) :: Bool
    
    morphisms = [morph for morph in keys(c.src) if !occursin("id", morph)]
    for i in morphisms
        for j in morphisms
            if c.target[i] == c.src[j]
                simplified = simplifyComposition(i, j, c.relations, c.identityRelations)

                if occursin("comp", simplified)
                    if debug
                        println("missing composition name: ")
                        println(thisComposition)
                        println(" ")
                    end
                    return false
                end
            end
        end
    end
    return true
end;

# Check that category c satisfies associativity by brute force
function checkAssociativity(c::Category, debug::Bool = false) :: Bool
    morphisms = keys(c.src)
    relations = c.relations
    identityRelations = c.identityRelations

    println("Checking associativity...")
    for i in morphisms
        for j in morphisms
            for k in morphisms
                if (c.target[i] == c.src[j]) && (c.target[j] == c.src[k])
                    println((k,j,i))
                    leftAssocLeft = simplifyComposition(i, j, relations, identityRelations)
                    leftAssoc = simplifyComposition(leftAssocLeft, k, relations, identityRelations)
                    rightAssocRight = simplifyComposition(j, k, relations, identityRelations)
                    rightAssoc = simplifyComposition(i, rightAssocRight, relations, identityRelations)
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

function productCategory(c::Category, d::Category)
    src = srcProduct(c, d)
    target = targetProduct(c, d)
    relations = relationsProduct(c, d)
    identityRelations = Vector{EqualityRule}([])
    productCat = categoryInit(src, target, relations, identityRelations, addIdentity=false)
    return productCat
end;

function srcProduct(c::Category, d::Category)
    srcKeys = [replace(string((i,j)), "\""=>"") for i in keys(c.src) for j in keys(d.src)]
    srcValues = [replace(string((i,j)), "\""=>"") for i in values(c.src) for j in values(d.src)]
    return Dict(zip(srcKeys, srcValues))
end

function targetProduct(c::Category, d::Category)
    targetKeys = [replace(string((i,j)), "\""=>"") for i in keys(c.target) for j in keys(d.target)]
    targetValues = [replace(string((i,j)), "\""=>"") for i in values(c.target) for j in values(d.target)]
    return Dict(zip(targetKeys, targetValues))
end

function relationsProduct(c::Category, d::Category)
    relations = Vector{EqualityRule}([])
    cRelations = c.relations ∪ c.identityRelations
    dRelations = d.relations ∪ d.identityRelations

    for cRelation in cRelations
        for dRelation in dRelations
            leftSecond = replace(string((cRelation.left.args[1], dRelation.left.args[1])), "\"" => "")
            leftFirst = replace(string((cRelation.left.args[2], dRelation.left.args[2])), "\"" => "")
            right = replace(string((cRelation.right, dRelation.right)), "\"" => "")
            thisRelation = @rule comp($leftSecond, $leftFirst)  == $right
            push!(relations, thisRelation)
        end
    end
    return relations
end;

println("Begin...")

src = Dict("f" => "0", "g" => "1", "h" => "2", "i" => "0", "k" => "1", "m" => "0", "n" => "0")
target = Dict("f" => "1", "g" => "2", "h" => "3", "i" => "2", "k" => "3", :"m" => "3", "n" => "3")

relations = @theory begin
    comp("g", "f") --> "i"
    comp("h", "g") --> "k"
    comp("h", "i") --> "m"
    comp("k", "f") --> "m" 
end

cat1 = categoryInit(src, target, relations, Vector{EqualityRule}([]), addIdentity=true);
cat2 = categoryInit(src, target, relations, Vector{EqualityRule}([]), addIdentity=true);

#productCat1Cat2 = productCategory(cat1, cat2)
#println(productCat1Cat2)

println("Done...")
