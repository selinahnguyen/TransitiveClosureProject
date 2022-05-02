#Selina Nguyen ID: 11659253
#CPTS 350 Spring 2022 BDD Project
from pyeda.inter import *

#this function creates a boolean expression for the given number and variable 
def get_formula(i,letter):
    temp=""
    index=0
    bin="{0:b}".format(i) #changing the number into binary
    difference=5-len(bin)
    
    if difference>0: #adding in zeros to binary number if the length is not 5
        for i in range(0,difference):
            bin='0'+bin

    for i in bin: #creating boolean formula
        if i=='1' and index<5:
            temp=temp+letter+"["+str(index)+"]"
        elif i=='0' and index<5:
            temp=temp+"~"+letter+"["+str(index)+"]" #adding negation if the number is 0
        if index<4:
            temp=temp+" & "
        index+=1
    return temp

# this function creates the boolean expression for the set of [prime] and [even]
def creat_even_prime_BDD(arr,letter):
    total=""
    for i in arr: #creating the boolean formula
        temp=get_formula(i,letter)
        if total=="":
            total+="("+temp+")"
        else:
            total+=" | "+"("+temp+")"
    return total
 
#this function is the helper function in creating the expression  for the RR BDD
def creat_formula(i,j):
    tempi=""
    tempj=""
    tempi=get_formula(i,"x")
    tempj=get_formula(j,"y")

    formula="((" + tempi + ")" + " & " + "(" + tempj + "))"
    return formula
#this function performs the composition of the two BDD's pasted in. Lecture 4/8/22
def composition(R,H):
    x = bddvars('x', 5)
    y = bddvars('y', 5)
    z = bddvars('z', 5)
    R=R.compose({x[0]:z[0], x[1]:z[1], x[2]:z[2], x[3]:z[3], x[4]:z[4]})
    H=H.compose({y[0]:z[0], y[1]:z[1], y[2]:z[2], y[3]:z[3], y[4]:z[4]})
    temp=(R & H).smoothing(z)
    return temp

#this function is the implementation fo the fixed point algorithm given from lecture 4/1/22
def fixed_point(R):
    H = R
    while True:
        h_prime = H
        H = h_prime | composition(R,h_prime)
        if H.equivalent(h_prime):
            return H

#testing function for RR and RR2
def RR_test(i,j,R,strr):
    temp=bdd2expr(R) #turn BDD back to an expr
    formula=creat_formula(i,j) #get formula for the numbers i and j passed in
    formula=expr(formula) #turn into an expression
    result=temp & formula#combine with an logical and
    if list(result.satisfy_all()):
        ret="Test case: "+strr+"("+str(i) +","+str(j)+") TRUE"
    else:
        ret="Test case: "+strr+"("+str(i) +","+str(j)+") FALSE"
    print(ret)

#testing function for [even] set
def even_test(num,E):
    temp=bdd2expr(E) #turn BDD back to an expr
    formula=get_formula(num,'y') #get formula for the number
    formula=expr(formula) #turn into an expression
    result=temp & formula #combine with an logical and
    if list(result.satisfy_all()):
        ret="Test case: EVEN("+str(num) +") TRUE"
    else:
        ret="Test case: EVEN("+str(num) +") FALSE"
    print(ret)

#testing function for [prime] set
def prime_test(num,P):
    temp=bdd2expr(P) #turn BDD back to an expression
    formula=get_formula(num,'x') #get formula expressions for test number
    formula=expr(formula) #turn num into an expression
    result=temp & formula #combine with an logical and
    if list(result.satisfy_all()):
        ret="Test case: PRIME("+str(num) +") TRUE"
    else:
        ret="Test case: PRIME("+str(num) +") FALSE"
    print(ret)




#creating the sets for [prime] and [even]
prime=[3,5,7,11,13,17,19,23,29,31]
even=[]
for i in range(0,31,2):
    even.append(i)

R="" #boolean expression for set R
E="" #boolean expression for set [even]
P="" #boolean expression for set [prime]

#these two forloops will create the boolean formula for the BDD RR 
for i in range(0,32):
    for j in range(0,32):
        if (((i + 3) % 32) == (j % 32)) or (((i + 8) % 32) == (j % 32)):
            temp=creat_formula(i,j)
            if R=="": #go into this if statement only at the first loop
                R+=temp
            else:
                R+=" | "+temp

#step3.1
print("*************************************** BDD Project Selina Nguyen ***************************************")
print("")
print("Step 3.1: Creating BDDs for the set of R, EVEN, and PRIME")
#creating RR BDD
RR=expr2bdd(expr(R))

#creating EVEN BDD
E=creat_even_prime_BDD(even,"y")
EVEN=expr2bdd(expr(E))

#creating PRIME BDD
P=creat_even_prime_BDD(prime,"x")
PRIME=expr2bdd(expr(P))

#testing part 1
RR_test(27,3,RR,"RR")
RR_test(16,20,RR,"RR")
even_test(14,EVEN)
even_test(13,EVEN)
prime_test(7,PRIME)
prime_test(2,PRIME)

#step 3.2
print("Step 3.2: Computing BDD RR2 for the set R ◦ R")

RR2=composition(RR,RR)
#testing part 2
RR_test(27,6,RR2,"RR2")
RR_test(27,9,RR2,"RR2")

#step 3.3
print("Step 3.3: Computing the transitive closure RR2star of RR2")
RR2Star = fixed_point(RR2)

#step 3.4
print("step 3.4: Computing the truth value to the following statement: ∀u. (PRIME(u) → ∃v. (EVEN(v)∧RR2star(u,v)))")
print("")

#code based on lecture 4/8/22
y = bddvars('y', 5)
v1=EVEN & RR2Star #(EVEN(v)∧RR2star(u,v))
v2=v1.smoothing(y) # ∃v. (EVEN(v)∧RR2star(u,v))
var=(~PRIME) | v2 #PRIME(u) → ∃v. (EVEN(v)∧RR2star(u,v))
result=var.equivalent(True) #∀u. (PRIME(u) → ∃v. (EVEN(v)∧RR2star(u,v))). -> result

#printing out results
if(result):
	print("       RESULT TRUE: Each node u in [prime] can be reached to a node v in [even] in a positive even number of steps")
else:
	print("       RESULT FALSE: Not all nodes are reachable in an positive even number of steps")
print("")
print("*********************************************************************************************************")



 