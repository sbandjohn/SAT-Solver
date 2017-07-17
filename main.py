# python3

import random
import copy
import sys

def clean(F):
	Fp = []
	for c in F:
		if not c: return False, None
		isTrue = False
		for x in c:
			if -x in c:                     # remove useless clauses 
				isTrue = True
				break
		if not isTrue:
			Fp.append(copy.deepcopy(c))
	return True, Fp

value = []        # record the value of variables
trueSet = set()                             # record literals which must be true
F = []                                      # CNF expression, list of clauses(set)
I = set()                                   # indexes of clauses which are still useful
S = {}                              # dict, S[x] is the set of clauses(indexes) which contain x

BCPCnt=0
BCPConflict=0
findCnt=0
findLayer=0
cnt = 0                             # count the times find() are called

def setTrue(x0):                    # set literal x0 to True
	flag = True
	if x0>0: value[x0] = True
	else: value[-x0] = False
	for j in S[x0]:                       # remove useless clauses from I 
		I.remove(j)
		for x in F[j]:                    # update S(x) for x in the removed clause
			if x!=x0:
				S[x].remove(j)
				if (len(S[x]) == 0) and (len(S[-x])>0):
					trueSet.add(-x)                      # -x is a pure literal
	for j in S[-x0]:                       # remove -x0 from clauses
		F[j].remove(-x0)
		if len(F[j]) == 1:                 # F[j] is a unit clause
			for x in F[j]:
				trueSet.add(x)
		if not F[j]: flag = False
	if flag == False: return False         # empty clause
	return None

def recover(x0):                    # set x0 back to undecided state
	if x0>0: value[x0] = None
	else: value[-x0] = None
	for j in S[x0]:
		I.add(j)
		for x in F[j]:
			if x!=x0:
				S[x].add(j)
	for j in S[-x0]:
		F[j].add(-x0)


def show():
	print("I:",I)
	for j in I:
		print(F[j])
	print()
	print("S:",S)
	print("T:",trueSet)
	print("v:",value)
	print()

	
def BCP_PURE(debug = False):    # BCP_PURE as a whole, make implied assignment continuously
	#global BCPCnt, BCPConfict
	#BCPCnt+=1
	#print("BCPCnt:", BCPCnt)
	trueList = []               # record the list of implied assignment
	global F, I, S, trueSet
	while trueSet:
		x0 = trueSet.pop()
		if x0>0:
			v = value[x0]
			exp = True
		else:
			v = value[-x0]
			exp = False
		if (v!=None) and (v!=exp):
			return False, trueList    # conflict in assigment
		if v == None:
			res = setTrue(x0)
			trueList.append(x0)
			if res == False: return False, trueList
			if debug:
				print("got:",x0)
				show()
	return True, trueList

def recoverBy(trueList):                  # recover to the state before BCP_PURE
	for i in range(len(trueList)-1, -1,-1):
		x0 = trueList[i]
		recover(x0)

def find(debug = False):
	global F, I, S, trueSet	
	#global findCnt, findLayer 
	#findCnt+=1
	#print("findCnt:", findCnt, "clause:", len(I))
	#print('findLayer:',findLayer)

	res, trueList = BCP_PURE(debug)

	if res == False:                       # conflict is found in BCP
		recoverBy(trueList)
		return False
	
	if not I:                              # no clauses left
		return True
	
	# now, trueSet is empty

	#x0 = chooseVariable()
	#x0 = chooseVariableGreedy()	
	#x0 = chooseVariableDouble()
	x0 = chooseVariableDoubleCombined()
	
	trueSet = set()
	res = setTrue(x0)
	if res == None:
		#findLayer+=1
		res = find(debug)
		#findLayer-=1
		if res: return True
	recover(x0)

	# now, trueSet should be set to empty because the previous one is irrelevant
	trueSet = set()
	res = setTrue(-x0)
	if res == None:
		#findLayer+=1
		res = find(debug)
		#findLayer-=1
		if res: return True
	recover(-x0)

	recoverBy(trueList)             # return to previous state for further search
	return False


alpha = 1.0
beta = 1.0

def chooseVariable():               # randomly pick one useful variable
	j = I.pop()
	x = F[j].pop()
	F[j].add(x)
	I.add(j)
	return x

def chooseVariableGreedy():
	maxv = 0
	choice  = 0
	for j in I:
		for x in F[j]:
			v = len(S[-x])*alpha + len(S[x])*beta
			if (v>maxv):
				maxv = v
				choice = x
	return choice

def chooseVariableDouble():
	minL = 2147483647
	choiceI = -1
	for j in I:
		if (len(F[j])<minL):
			minL = len(F[j])
			choiceI = j
	maxv = -2147483647
	choice = 0
	for x in F[choiceI]:
		v = len(S[-x])*alpha + len(S[x])*beta
		if (v>maxv):
			maxv = v
			choice = x
	return choice

def chooseVariableDoubleCombined():         # method of choosing finally used
	minL = 2147483647
	choiceI = -1
	cntI=0
	for j in I:                         # calculate the smallest size of clauses
		if (len(F[j])<minL):
			cntI = 1
			minL = len(F[j])
			choiceI = j
		elif len(F[j]) == minL:
			cntI += 1
	rate = float(cntI)/float(len(I))
	if rate>0.80:                       # if so many smallest clauses, randomly choose
		return chooseVariable()
	maxv = -2147483647
	choice = 0
	for j in I:                         # from smallest clauses, find "best" literal
		if (len(F[j])==minL):
			for x in F[j]:
				v = len(S[-x])*alpha + len(S[x])*beta
				if (v>maxv):
					maxv = v
					choice = x
	return choice
	if len(S[choice]) > len(S[-choice]): return choice
	else: return -choice

def assign(F,v):                   # assignment, to check whether the answer is correct
	#print("assign:",F)
	#print(v)
	for c in F:
		tmp = False
		for x in c:
			if (v[abs(x)]!=None):
				if x>0: value = v[x]
				else: value = not v[-x]
				tmp = tmp or value
				if tmp: break
		if not tmp: return False
	return True

def solve(F0):
	global F, I, S, trueSet, value
	can, F = clean(F0)
	if can:
		S={}
		I=set()
		maxX = 0
		for j in range(len(F)):            #initialize S, I, tureSet and value
			I.add(j)
			for x in F[j]:
				if x not in S:
					S[x] = set()
				if -x not in S:
					S[-x] = set()
				maxX = max(maxX, abs(x))
				S[x].add(j)
		value = [None for i in range(maxX+1)]

		trueSet = set()
		for x in S:
			if (len(S[x]) > 0) and (len(S[-x])==0): trueSet.add(x)
		for j in range(len(F)):
			if len(F[j])==1:
				for x in F[j]:
					trueSet.add(x)

		can = find(debug=False)
	#print(cnt)
	if can:
		print("s SATISFIABLE")
		#print("sat:",value)
		#print(assign(F0,value))
		return True
	else:
		print("s UNSATISFIABLE")
		return False

def readCNF(f):                              # CNF parser for DIMACS format
	F = []
	cur = set()
	for s in f:
		if len(s)==0 or s[0]=='c': continue
		if s[0] == 'p':
			a,b,c,d = s.split()
			n = int(c)
			m = int(d)
			continue
		if s[0]=='%': continue
		tmp = list(map(int,s.split()))
		for x in tmp:
			if x==0:
				F.append(copy.deepcopy(cur))
				cur = set()
				m-=1
				if (m==0): return F
			else:
				cur.add(x)

if __name__ == "__main__":
	inputName = sys.argv[1]
	with open(inputName, 'r') as f:
		F0 = readCNF(f)
		solve(F0)

