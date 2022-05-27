from tkinter import ttk
from tkinter import *
import sys
import matplotlib
from pyvis.network import Network
matplotlib.use("TKAgg")
import tkinter as tk
import nltk
import re


net = Network(directed=True)
T= Network(directed=True)

def removeLeftRecursion(rulesDiction):
   # for rule: A->Aa|b
   # result: A->bA',A'->aA'|#

   # 'store' has new rules to be added
   store = {}
   # traverse over rules
   for lhs in rulesDiction:
      # alphaRules stores subrules with left-recursion
      # betaRules stores subrules without left-recursion
      alphaRules = []
      betaRules = []
      # get rhs for current lhs
      allrhs = rulesDiction[lhs]
      for subrhs in allrhs:
         if subrhs[0] == lhs:
            alphaRules.append(subrhs[1:])
         else:
            betaRules.append(subrhs)
      # alpha and beta containing subrules are separated
      # now form two new rules
      if len(alphaRules) != 0:
         # to generate new unique symbol
         # add ' till unique not generated
         lhs_ = lhs + "'"
         while (lhs_ in rulesDiction.keys()) \
               or (lhs_ in store.keys()):
            lhs_ += "'"
         # make beta rule
         for b in range(0, len(betaRules)):
            betaRules[b].append(lhs_)
         rulesDiction[lhs] = betaRules
         # make alpha rule
         # for rule: A->Aa|b
         # result: A->bA',A'->aA'|#
         for a in range(0, len(alphaRules)):
            alphaRules[a].append(lhs_)
         alphaRules.append(['#'])
         # store in temp dict, append to
         # - rulesDiction at end of traversal
         store[lhs_] = alphaRules
   # add newly generated rules generated
   # - after removing left recursion
   for left in store:
      rulesDiction[left] = store[left]
   return rulesDiction


def LeftFactoring(rulesDiction):
   # for rule: A->aDF|aCV|k
   # result: A->aA'|k, A'->DF|CV

   # newDict stores newly generated
   # - rules after left factoring
   newDict = {}
   # iterate over all rules of dictionary
   for lhs in rulesDiction:
      # get rhs for given lhs
      allrhs = rulesDiction[lhs]
      # temp dictionary helps detect left factoring
      temp = dict()
      for subrhs in allrhs:
         if subrhs[0] not in list(temp.keys()):
            temp[subrhs[0]] = [subrhs]
         else:
            temp[subrhs[0]].append(subrhs)
      # if value list count for any key in temp is > 1,
      # - it has left factoring
      # new_rule stores new subrules for current LHS symbol
      new_rule = []
      # temp_dict stores new subrules for left factoring
      tempo_dict = {}
      for term_key in temp:
         # get value from temp for term_key
         allStartingWithTermKey = temp[term_key]
         if len(allStartingWithTermKey) > 1:
            # left factoring required
            # to generate new unique symbol
            # - add ' till unique not generated
            lhs_ = lhs + "'"
            while (lhs_ in rulesDiction.keys()) \
                  or (lhs_ in tempo_dict.keys()):
               lhs_ += "'"
            # for rule: A->aDF|aCV|k
            # result: A->aA'|k, A'->DF|CV
            # append the left factored result
            new_rule.append([term_key, lhs_])
            # add expanded rules to tempo_dict
            ex_rules = []
            for g in temp[term_key]:
               ex_rules.append(g[1:])
            tempo_dict[lhs_] = ex_rules
         else:
            # no left factoring required
            new_rule.append(allStartingWithTermKey[0])
      # add original rule
      newDict[lhs] = new_rule
      # add newly generated rules after left factoring
      for key in tempo_dict:
         newDict[key] = tempo_dict[key]
   return newDict


def first(rule):
   global rules, nonterm_userdef, \
      term_userdef, diction, firsts
   # recursion base condition
   # (for terminal or epsilon)
   if len(rule) != 0 and (rule is not None):
      if rule[0] in term_userdef:
         return rule[0]
      elif rule[0] == '#':
         return '#'

   # condition for Non-Terminals
   if len(rule) != 0:
      if rule[0] in list(diction.keys()):
         # fres temporary list of result
         fres = []
         rhs_rules = diction[rule[0]]
         # call first on each rule of RHS
         # fetched (& take union)
         for itr in rhs_rules:
            indivRes = first(itr)
            if type(indivRes) is list:
               for i in indivRes:
                  fres.append(i)
            else:
               fres.append(indivRes)

         # if no epsilon in result
         # - received return fres
         if '#' not in fres:
            return fres
         else:
            # apply epsilon
            # rule => f(ABC)=f(A)-{e} U f(BC)
            newList = []
            fres.remove('#')
            if len(rule) > 1:
               ansNew = first(rule[1:])
               if ansNew != None:
                  if type(ansNew) is list:
                     newList = fres + ansNew
                  else:
                     newList = fres + [ansNew]
               else:
                  newList = fres
               return newList
            # if result is not already returned
            # - control reaches here
            # lastly if eplison still persists
            # - keep it in result of first
            fres.append('#')
            return fres


def follow(nt):
   global start_symbol, rules, nonterm_userdef, \
      term_userdef, diction, firsts, follows
   # for start symbol return $ (recursion base case)

   solset = set()
   if nt == start_symbol:
      solset.add('$')


   # For input, check in all rules
   for curNT in diction:
      rhs = diction[curNT]
      # go for all productions of NT
      for subrule in rhs:
         if nt in subrule:
            # call for all occurrences on
            # - non-terminal in subrule
            while nt in subrule:
               index_nt = subrule.index(nt)
               subrule = subrule[index_nt + 1:]
               # empty condition - call follow on LHS
               if len(subrule) != 0:
                  # compute first if symbols on
                  # - RHS of target Non-Terminal exists
                  res = first(subrule)
                  # if epsilon in result apply rule
                  # - (A->aBX)- follow of -
                  # - follow(B)=(first(X)-{ep}) U follow(A)
                  if '#' in res:
                     newList = []
                     res.remove('#')
                     ansNew = follow(curNT)
                     if ansNew != None:
                        if type(ansNew) is list:
                           newList = res + ansNew
                        else:
                           newList = res + [ansNew]
                     else:
                        newList = res
                     res = newList
               else:
                  # when nothing in RHS, go circular
                  # - and take follow of LHS
                  # only if (NT in LHS)!=curNT
                  if nt != curNT:
                     res = follow(curNT)

               # add follow result in set form
               if res is not None:
                  if type(res) is list:
                     for g in res:
                        solset.add(g)
                  else:
                     solset.add(res)
   return list(solset)


def computeAllFirsts(flag):
   global rules, nonterm_userdef, \
      term_userdef, diction, firsts
   RulesList = []
   LeftRecList = []
   LeftFactList = []
   FirstsList = []

   for rule in rules:
      k = rule.split("->")
      # remove un-necessary spaces
      k[0] = k[0].strip()
      k[1] = k[1].strip()
      rhs = k[1]
      multirhs = rhs.split('|')
      # remove un-necessary spaces
      for i in range(len(multirhs)):
         multirhs[i] = multirhs[i].strip()
         multirhs[i] = multirhs[i].split()
      diction[k[0]] = multirhs

   print(f"\nRules: \n")
   RulesList.append("Rules :\n")
   for y in diction:
      RulesList.append([f"{y}->{diction[y]} \n"])
      print(f"{y}->{diction[y]}")


   print(f"\nAfter elimination of left recursion:\n")

   diction = removeLeftRecursion(diction)
   LeftRecList.append(" After elimination of left recursion: \n")
   for y in diction:
      LeftRecList.append([f"{y}->{diction[y]} \n "])
      print(f"{y}->{diction[y]}")


   print("\nAfter left factoring:\n")

   diction = LeftFactoring(diction)
   LeftFactList.append(" After left factoring: \n")
   for y in diction:
      LeftFactList.append([f" {y}->{diction[y]} \n"])
      print(f"{y}->{diction[y]}")

   # calculate first for each rule
   # - (call first() on all RHS)
   for y in list(diction.keys()):
      t = set()
      for sub in diction.get(y):
         res = first(sub)
         if res != None:
            if type(res) is list:
               for u in res:
                  t.add(u)
            else:
               t.add(res)

      # save result in 'firsts' list
      firsts[y] = t

   print("\nCalculated firsts: ")
   key_list = list(firsts.keys())
   index = 0
   FirstsList.append("\n \n Calculated firsts:  \n")
   for gg in firsts:
      FirstsList.append([f" \n first({key_list[index]}) "f"=> {firsts.get(gg)} \n"])
      print(f"first({key_list[index]}) "f"=> {firsts.get(gg)}")
      index += 1

   if (flag == 0):
       return RulesList
   elif(flag == 1):
      return LeftRecList
   elif(flag == 2):
      return LeftFactList
   elif(flag == 3):
      return FirstsList
   else:
      return RulesList,LeftRecList,LeftFactList,FirstsList



def computeAllFollows():
   global start_symbol, rules, nonterm_userdef,\
      term_userdef, diction, firsts, follows

   FollowsList = []

   for NT in diction:
      solset = set()
      sol = follow(NT)
      if sol is not None:
         for g in sol:
            solset.add(g)
      follows[NT] = solset

   print("\nCalculated follows: ")
   key_list = list(follows.keys())
   index = 0
   FollowsList.append("Calculated follows:  \n")
   for gg in follows:
      FollowsList.append([f" \n follow({key_list[index]})"f" => {follows[gg]} \n"])
      print(f"follow({key_list[index]})"
         f" => {follows[gg]}")
      index += 1
   return FollowsList

# create parse table
def createParseTable():
   import copy
   global diction, firsts, follows, term_userdef
   print("\nFirsts and Follow Result table\n")

   with open('firstnFollow.txt', 'w') as f:

      f.write('\n')

      # PRINTS FIRSTS AND FOLLOWS
      mx_len_first = 0
      mx_len_fol = 0
      for u in diction:
         k1 = len(str(firsts[u]))
         k2 = len(str(follows[u]))
         if k1 > mx_len_first:
            mx_len_first = k1
         if k2 > mx_len_fol:
            mx_len_fol = k2
      FFTableList = []

      FFTableList.append(f"{{:<{10}}} "f"{{:<{mx_len_first + 15}}} "f"{{:<{mx_len_fol + 15}}} \n ".format("Non-T", "FIRST", "FOLLOW"))
      print(f"{{:<{10}}} "f"{{:<{mx_len_first + 5}}} "f"{{:<{mx_len_fol + 5}}}".format("Non-T", "FIRST", "FOLLOW"))
      f.writelines(f"{{:<{10}}} "f"{{:<{mx_len_first + 5}}} "f"{{:<{mx_len_fol + 5}}} \n".format("Non-T", "FIRST", "FOLLOW"))
      for u in diction:
         FFTableList.append([f"\n{{:<{10}}} "f"{{:<{mx_len_first + 15}}} "f"{{:<{mx_len_fol + 25}}}\n".format(u, str(firsts[u]), str(follows[u]))])
         print(f"{{:<{10}}} "f"{{:<{mx_len_first + 5}}} "f"{{:<{mx_len_fol + 5}}}".format(u, str(firsts[u]), str(follows[u])))
         f.writelines(f"{{:<{10}}} "f"{{:<{mx_len_first + 5}}} "f"{{:<{mx_len_fol + 5}}}\n".format(u, str(firsts[u]), str(follows[u])))


      # create matrix of row(NT) x [col(T) + 1($)]
      # create list of non-terminals
      ntlist = list(diction.keys())
      terminals = copy.deepcopy(term_userdef)
      terminals.append('$')

      # create the initial empty state of ,matrix
      mat = []
      for x in diction:
         row = []
         for y in terminals:
            row.append('')
         # of $ append one more col
         mat.append(row)

      # Classifying grammar as LL(1) or not LL(1)
      grammar_is_LL = True

      # rules implementation
      for lhs in diction:
         rhs = diction[lhs]
         for y in rhs:
            res = first(y)
            # epsilon is present,
            # - take union with follow
            if '#' in res:
               if type(res) == str:
                  firstFollow = []
                  fol_op = follows[lhs]
                  if fol_op is str:
                     firstFollow.append(fol_op)
                  else:
                     for u in fol_op:
                        firstFollow.append(u)
                  res = firstFollow
               else:
                  res.remove('#')
                  res = list(res) +\
                     list(follows[lhs])
            # add rules to table
            ttemp = []
            if type(res) is str:
               ttemp.append(res)
               res = copy.deepcopy(ttemp)
            for c in res:
               xnt = ntlist.index(lhs)
               yt = terminals.index(c)
               if mat[xnt][yt] == '':
                  mat[xnt][yt] = mat[xnt][yt] \
                           + f"{lhs}->{' '.join(y)}"
               else:
                  # if rule already present
                  if f"{lhs}->{y}" in mat[xnt][yt]:
                     continue
                  else:
                     grammar_is_LL = False
                     mat[xnt][yt] = mat[xnt][yt] \
                              + f",{lhs}->{' '.join(y)}"

      # f.close()
   r = open('firstnFollow.txt', 'r')
   ff = r.read()
   print(ff)

      # final state of parse table
   with open('parseTable.txt', 'w') as p:

      p.write('\n')

      ParseTableList = []
      ParseTableList.append("Generated parsing table:\n")
      print("\nGenerated parsing table:\n")
      p.writelines("\nGenerated parsing table:\n")
      frmt = "{:>35}" * len(terminals)
      ParseTableList.append(["\n"+frmt.format(*terminals)+"\n"])
      print(frmt.format(*terminals))
      p.writelines(frmt.format(*terminals)+"\n")

      j = 0
      for y in mat:
         frmt1 = "{:>35}" * len(y)
         ParseTableList.append([f"\n{ntlist[j]} {frmt1.format(*y)}\n"])
         print(f"{ntlist[j]} {frmt1.format(*y)}")
         p.writelines(f"{ntlist[j]} {frmt1.format(*y)} \n")
         j += 1
      p.close()

      pT = open('parseTable.txt', 'r')
      t = pT.read()
      print(t)

   return (mat, grammar_is_LL, terminals),FFTableList,ParseTableList,t,ff


def divText(Source_Code):
   patternID = r"(^[^\d\W]\w*\Z)"  # for Identifier
   patternNum = r"[0.0-9.9]+"  # for NUM and Decimals
   patternOP = r"[+\-\*\/]"
   patternParenthesis1 = r"[\(]"
   patternParenthesis2 = r"[\)]"

   for line in Source_Code:
      tokenList= nltk.wordpunct_tokenize(line)
      print(tokenList)

   tokenType = ["" for x in range(len(tokenList))]
   for i in range(0, len(tokenList)):
      if (tokenList[i] == '-'):
         tokenType[i] = '-'
      else:
         if (tokenList[i] == '+'):
            tokenType[i] = '+'
         else:
            if (tokenList[i] == '/'):
               tokenType[i] = '/'
            else:
               if (tokenList[i] == '*'):
                  tokenType[i] = '*'
               else:
                    if re.fullmatch(patternID, tokenList[i]):
                        tokenType[i] = 'Identifier'
                    else:
                        if (re.fullmatch(patternNum,tokenList[i])):
                              tokenType[i] = 'Number'
                        else:
                           if re.fullmatch(patternParenthesis1, tokenList[i]):
                              tokenType[i] = '('
                           else:
                              if re.fullmatch(patternParenthesis2, tokenList[i]):
                                 tokenType[i] = ')'
                              else:
                                 tokenType[i] = 'INVALIDID'
   print (tokenType)
   return tokenType
##########################################################################################

def divText1(Source_Code):
   patternID = r"(^[^\d\W]\w*\Z)"  # for Identifier
   patternNum = r"[0.0-9.9]+"  # for NUM and Decimals
   patternOP = r"[+\-\*\/]"
   patternParenthesis1 = r"[\(]"
   patternParenthesis2 = r"[\)]"

   for line in Source_Code:
      tokenList= nltk.wordpunct_tokenize(line)
      print(tokenList)

   tokenType = ["" for x in range(len(tokenList))]
   for i in range(0, len(tokenList)):
      if (tokenList[i] == '-'):
         tokenType[i] = '-'
      else:
         if (tokenList[i] == '+'):
            tokenType[i] = '+'
         else:
            if (tokenList[i] == '/'):
               tokenType[i] = '/'
            else:
               if (tokenList[i] == '*'):
                  tokenType[i] = '*'
               else:
                    if re.fullmatch(patternID, tokenList[i]):
                        tokenType[i] = 'Identifier'
                    else:
                        if (re.fullmatch(patternNum,tokenList[i])):
                              tokenType[i] = 'Number'
                        else:
                           if re.fullmatch(patternParenthesis1, tokenList[i]):
                              tokenType[i] = '('
                           else:
                              if re.fullmatch(patternParenthesis2, tokenList[i]):
                                 tokenType[i] = ')'
                              else:
                                 tokenType[i] = 'INVALIDID'
      # print (tokenType)
   DrawSyntaxTree(tokenList)

OpList=0
OpList1=0
NumList=[]
NumList1=[]
Operations=[]
u=0
b=0
h=0
c=0
counterNum=0
mi=0
max=0
titi=0
SavedOperation=0
SavedOperation1=0
SavedOperation2=0
brackets=0
indexlist=[]
FlagNum=False
f5=False
FlagTokens=False
flagY=False
Flagaya=False
Flagaya1=False
ayHaga=False
am=False
aM=False
def DrawSyntaxTree(tokens):

   global c,u,b,h,am,mi,aM,OpList,OpList1,FlagNum,Flagaya,Flagaya1,FlagTokens,flagY,ayHaga,counterNum,NumList,NumList1,Operations,SavedOperation,idexlist,SavedOperation1,brackets,SavedOperation2,f5
   patternNum = r"[0.0-9.9]+"
   patternID = r"(^[^\d\W]\w*\Z)"
   for ze in range(0,len(tokens)):
      if(tokens[ze]=='*' or tokens[ze]=='/' or tokens[ze]=='+' or tokens[ze]=='-'):
         Operations.append(tokens[ze])
      if(tokens[ze]==')'):
         brackets=brackets+1

      if(tokens[ze]=='*' or tokens[ze]=='/'):
         c=c+1


   if(Operations[0]=="*" or Operations[0]=="/"):
      ayHaga=True


   for i in range(0, len(Operations)-1):
      if(Operations[i]==Operations[i+1] and (Operations[i]!='*' or Operations[i]!='/')):
         indexlist.append(i)


   for i in range (0,len(tokens)):
      if (tokens[i]==')' and i < len(tokens)-1 and (tokens[i + 1] == '-' or tokens[i + 1] == '+')):
         b = u + 1
         u = b + 1
         T.add_node(b, tokens[i + 1])
         if(brackets>1 and i!=len(tokens)-3):
            SavedOperation1=b
         # if(len(tokens)-i<4):
         #    T.add_edge(b,h)
         OpList = b
         OpList1 = tokens[i + 1]
         FlagTokens = True
         h = OpList
         continue

      elif (tokens[i]==')' and  i == len(tokens)-1):
         continue

      if(tokens[i]=='('):
         SavedOperation=b
         continue

      if (tokens[i] == '*' or tokens[i] == '/'):
         continue

      if(c>=2):
         Flagaya=True
         if (aM == True):
            u = u + 1
            T.add_node(u, tokens[i])
            T.add_edge(mi, u)
            aM = False
            if(i==len(tokens)-1):
               break
            b = u + 1
            u = b + 1
            if (i == len(tokens) - 3):
               T.add_node(b, tokens[i + 1], color='Red')
               T.add_edge(b, h)
               T.add_node(u, tokens[i + 2])
               T.add_edge(b, u)
               u = u + 1
            Flagaya1=True


      if(Flagaya==False):
         if(aM==True):
            u=u+1
            T.add_node(u,tokens[i])
            T.add_edge(mi, u)
            aM=False
            b = u + 1
            u = b + 1
            if (i == len(tokens) - 3):
               T.add_node(b, tokens[i + 1], color='Red')
               T.add_edge(b, h)
               T.add_node(u,tokens[i+2])
               T.add_edge(b,u)
               u=u+1
               break
            if(i==len(tokens)-1 or (tokens[i+1]==')' and tokens[i+1]==len(tokens)-1) ):
               break
            else:
               continue

      if(am==True):
         u=u+1
         T.add_node(u,tokens[i])
         T.add_edge(mi, u)
         u= u+1
         aM=True
         am=False
         continue

      if((tokens[i]=='-' or tokens[i]=='+') and i != len(tokens)-2):

         for e in range(0,len(Operations)-1):
            # if(tokens[i]==Operations[e] and indexlist==e):
            #    print
            #    break
            # else:
            if(tokens[i]==Operations[e] and(Operations[e+1]=='+'or Operations[e+1]=='-')):
               if( len(indexlist)!=0):
                  Operations[e] = 0
                  break
            else:

               if(tokens[i]==Operations[e] and(Operations[e+1]=='*'or Operations[e+1]=='/')):

                  mi= u + 1
                  u= mi + 1

                  T.add_node(mi, Operations[e + 1])
                  # if(c>=2 and e > 1):
                  #    b = u + 1
                  #    u= b + 1
                  #    T.add_node(b,tokens[i])
                  #    T.add_edge(b,mirna)
                  #    T.add_edge(b,h)
                  #    break
                  # else:
                  T.add_edge(b, mi)
                  Operations[e]=0
                  Operations[e+1]=0
                  am=True
                  break

         continue

      if(i == len(tokens)-2):

         u=u+1
         T.add_node(u,tokens[i+1])
         T.add_edge(b,u)
         if(tokens[i-1]==')'):
            T.add_edge(b,SavedOperation)
         if (brackets>1):
            # T.add_edge(SavedOperation,SavedOperation1)
            T.add_edge(SavedOperation1,SavedOperation2)

         break

      if(Flagaya1==False):

         if(re.fullmatch(patternNum,tokens[i]) or  re.fullmatch(patternID,tokens[i])):

            T.add_node(u,tokens[i])
            NumList.append([tokens[i]])
            NumList1.append(u)
            counterNum=counterNum+1
            u=u+1
            FlagNum=True
      if(i<len(tokens)-1):
         if(tokens[i+1] == '-' or tokens[i+1] == '+' or (tokens[i+1]=="*"and ayHaga==True) or (tokens[i+1]=="/"and ayHaga==True)):
            b=u+1
            u=b+1
            if(i==len(tokens)-3):
               T.add_node(b, tokens[i + 1],color='Red')
            else:
               if(tokens[i-1]=='('):
                  SavedOperation2=b
               T.add_node(b,tokens[i+1])
               OpList=b
               OpList1=tokens[i+1]
               FlagTokens=True
      if(i==0):
         T.add_edge(b, NumList1[i])

      if (i!=0):
         if(tokens[i-1]=='('):
            # T.add_edge(h, b)
            FlagNum = True
            # if (len(NumList) > 1):
            T.add_edge(b, NumList1[counterNum - 1])
            if(brackets==1):
               T.add_edge(SavedOperation,b)
            f5=True
         if(tokens[i+1]==')' and i!=len(tokens)-2):
            T.add_edge(SavedOperation, b)
            T.add_edge(b, NumList1[counterNum - 1])
         elif(f5==False):
            T.add_edge(b,h)
            FlagNum=True
            if(len(NumList)>1):
               T.add_edge(h,NumList1[counterNum-1])

      if(FlagNum==True and FlagTokens==True):
            if(tokens[i+1]==OpList1):
               h=OpList



      f5=False
      FlagNum=False
      FlagTokens=False

   T.show("SyntaxTree.html")





flagx=False

def validateStringUsingStackBuffer(parsing_table, grammarll1,
                        table_term_list, input_string,
                        term_userdef,start_symbol,returned_tokenList):
   global flagx
   ValidationList = []
   # window2 = tk.Toplevel()
   # canvas2 = Canvas(window2, width=500, height=500)

   # canvas2.pack(side="top", fill="both", expand=True, padx=40, pady=40)

   with open('stack.txt', 'w') as f:

      f.write('\n')

      ValidationList.append(f"\nValidate String => {input_string}\n")
      print(f"\nValidate String => {input_string}\n")
      f.writelines(f"\nValidate String => {input_string}\n")

      # for more than one entries
      # - in one cell of parsing table
      if grammarll1 == False:
         return f"\nInput String = " \
                f"\"{input_string}\"\n" \
                f"Grammar is not LL(1)"

      # implementing stack buffer

      stack = [start_symbol, '$']
      buffer = []

      # reverse input string store in buffer
      # input_string = input_string.split()
      # input_string.reverse()

      returned_tokenList.reverse()
      buffer = ['$'] + returned_tokenList
      if (stack[0] == 'exp' and flagx == False):
         print(ValidationList)
         ValidationList.append("{:>100} {:>100} {:>100}".format("Buffer", "Stack", "Action", '\n'))
         # f.writelines("{:>100} {:>100} {:>100}".format("Buffer", "Stack", "Action", '\n'))
         flagx = True

      # label50 = tk.Label(canvas2, text=ValidationList, justify=LEFT)
      # label50.pack()
      print("{:>40} {:>40} {:>40}".format("Buffer", "Stack", "Action"))
      f.writelines("{:>60} {:>60} {:>60}".format("Buffer", "Stack", "Action \n"))

      while True:
         # end loop if all symbols matched
         if stack == ['$'] and buffer == ['$']:
            ValidationList.append("{:>100} {:>100} {:>100} ".format(' '.join(buffer), ' '.join(stack), "Valid"))
            # label39 = tk.Label(canvas2, text=ValidationList, justify=LEFT)
            # label39.pack()
            print("{:>40} {:>40} {:>45}".format(' '.join(buffer), ' '.join(stack), "Accepted"))
            f.writelines("{:>60} {:>60} {:>65}".format(' '.join(buffer), ' '.join(stack), "Accepted",'\n'))
            f.writelines( "\nValid String!")
            return "\nValid String!"
         elif stack[0] not in term_userdef:
            # take font of buffer (y) and tos (x)
            x = list(diction.keys()).index(stack[0])
            y = table_term_list.index(buffer[-1])
            if parsing_table[x][y] != '':
               # format table entry received
               entry = parsing_table[x][y]
               ValidationList.append("{:>100} {:>100} {:100}".
                                     format(' '.join(buffer),
                                            ' '.join(stack),
                                            f"T[{stack[0]}][{buffer[-1]}] = {entry} \n"))
               # label41 = tk.Label(canvas2, text=ValidationList, anchor='w', justify=LEFT)
               # label41.pack()
               print("{:>40} {:>40} {:>45}".
                     format(' '.join(buffer),
                            ' '.join(stack),
                            f"T[{stack[0]}][{buffer[-1]}] = {entry}"))
               f.writelines("{:>60} {:>60} {:>65}".
                     format(' '.join(buffer),
                            ' '.join(stack),
                            f"T[{stack[0]}][{buffer[-1]}] = {entry} \n"))
               lhs_rhs = entry.split("->")
               lhs_rhs[1] = lhs_rhs[1].replace('#', '').strip()
               entryrhs = lhs_rhs[1].split()
               stack = entryrhs + stack[1:]
            else:
               ValidationList.append(f"\nInvalid String! No rule at " \
                                     f"Table[{stack[0]}][{buffer[-1]}].")  # Label on canvas invalid string
               f.writelines(f"\nInvalid String! No rule at " \
                                     f"Table[{stack[0]}][{buffer[-1]}].\n")
               return f"\nInvalid String! No rule at "f"Table[{stack[0]}][{buffer[-1]}]."
         else:
            # stack top is Terminal
            if stack[0] == buffer[-1]:
               ValidationList.append("{:>100} {:>100} {:>100}"
                                     .format(' '.join(buffer),
                                             ' '.join(stack),
                                             f"Matched:{stack[0]} \n"))
               # label45 = tk.Label(canvas2, text=ValidationList)
               # label45.pack()
               print("{:>40} {:>40} {:>45}"
                     .format(' '.join(buffer),
                             ' '.join(stack),
                             f"Matched:{stack[0]},pop[{stack[0]}]"))
               f.writelines("{:>60} {:>60} {:>65}"
                     .format(' '.join(buffer),
                             ' '.join(stack),
                             f"Matched:{stack[0]} ,pop[{stack[0]}]\n"))
               buffer = buffer[:-1]
               stack = stack[1:]
            else:
               ValidationList.append("\nInvalid String! " \
                                     "Unmatched terminal symbols")
               f.writelines("\nInvalid String! " \
                                     "Unmatched terminal symbols")
               # label49 = tk.Label(canvas2, text=ValidationList, justify=LEFT)
               # label49.pack()
               return "\nInvalid String! " \
                      "Unmatched terminal symbols"
      return ValidationList

# hena el function el bteb3att el actions el bnersem menha el parse Tree
def validateStringUsingStackBuffer1(parsing_table, grammarll1,
                        table_term_list, input_string,
                        term_userdef,start_symbol,returned_tokenList):
   ValidationList = []

   ValidationList.append(f"\nValidate String => {input_string}\n")
   print(f"\nValidate String => {input_string}\n")

   # for more than one entries
   # - in one cell of parsing table
   if grammarll1 == False:
      return f"\nInput String = " \
         f"\"{input_string}\"\n" \
         f"Grammar is not LL(1)"

   # implementing stack buffer

   stack = [start_symbol, '$']
   buffer = []

   # reverse input string store in buffer
   # input_string = input_string.split()
   # input_string.reverse()

   returned_tokenList.reverse()
   buffer = ['$'] + returned_tokenList

   ValidationList.append("{:>100} {:>100} {:>100}".format("Buffer", "Stack","Action",'\n'))
   # label50 = tk.Label(canvas2, text=ValidationList,justify=LEFT)
   # label50.pack()
   print("{:>40} {:>40} {:>40}".format("Buffer", "Stack","Action"))

   while True:
      # end loop if all symbols matched
      if stack == ['$'] and buffer == ['$']:
         ValidationList.append("{:>100} {:>100} {:>100} ".format(' '.join(buffer),' '.join(stack),"Valid"))

         print("{:>40} {:>40} {:>45}".format(' '.join(buffer),' '.join(stack),"Valid"))
         ParseTree("Valid")
         return "\nValid String!"
      elif stack[0] not in term_userdef:
         # take font of buffer (y) and tos (x)
         x = list(diction.keys()).index(stack[0])
         y = table_term_list.index(buffer[-1])
         if parsing_table[x][y] != '':
            # format table entry received
            entry = parsing_table[x][y]
            ParseTree(entry)
            ValidationList.append("{:>100} {:>100} {:100}".
               format(' '.join(buffer),
                     ' '.join(stack),
                     f"T[{stack[0]}][{buffer[-1]}] = {entry} \n"))
            print("{:>40} {:>40} {:>45}".
               format(' '.join(buffer),
                     ' '.join(stack),
                     f"T[{stack[0]}][{buffer[-1]}] = {entry}"))
            lhs_rhs = entry.split("->")
            lhs_rhs[1] = lhs_rhs[1].replace('#', '').strip()
            entryrhs = lhs_rhs[1].split()
            stack = entryrhs + stack[1:]
         else:
            ValidationList.append(f"\nInvalid String! No rule at " \
               f"Table[{stack[0]}][{buffer[-1]}].")  # Label on canvas invalid string
            return f"\nInvalid String! No rule at "f"Table[{stack[0]}][{buffer[-1]}]."
      else:
         # stack top is Terminal
         if stack[0] == buffer[-1]:
            ValidationList.append("{:>100} {:>100} {:>100}"
               .format(' '.join(buffer),
                     ' '.join(stack),
                     f"Matched:{stack[0]} \n"))
            print("{:>40} {:>40} {:>45}"
               .format(' '.join(buffer),
                     ' '.join(stack),
                     f"Matched:{stack[0]}"))
            buffer = buffer[:-1]
            stack = stack[1:]
         else:
            ValidationList.append("\nInvalid String! " \
               "Unmatched terminal symbols")
            return "\nInvalid String! " \
               "Unmatched terminal symbols"

   return ValidationList
# (left factoring & recursion present)



rules = ["exp -> exp addop term | term",
         "addop -> + | -",
         "term -> term mullop factor | factor",
         "mullop -> * | /",
         "factor -> ( exp ) | Identifier | Number"]

nonterm_userdef = ['exp', 'addop', 'term', 'mullop', 'factor']
term_userdef = ['Identifier', 'Number', '/', '*', '+', '-', ')', '(']

diction = {}
firsts = {}
follows = {}

RulesList,LeftRecList,LeftFactList,FirstsList = computeAllFirsts(11)

# computeAllFirsts(11)
# assuming first rule has start_symbol
# start symbol can be modified in below line of code
start_symbol = list(diction.keys())[0]
computeAllFollows()


(parsing_table, result, tabTerm),FFTableList,ParseTableList,t,ff = createParseTable()


def hide_me(root, button1,button2):
   # print('hide me')
   button1.place_forget()
   button2.place_forget()


def create_new_window(entry):

   sample_input_string = entry

   tokenList = sample_input_string

   scannedTokens = tokenList.split('\n')
   Source_Code = []
   for line in scannedTokens:
      Source_Code.append(line)
      divText(Source_Code)

   returned_tokenList = divText(Source_Code)

   button6 = tk.Button(root, text="   Syntax Tree   ", command=lambda: onClick1(entry),bg="LightGreen")
   # button6.pack(side='bottom')

   button5 = tk.Button(root, text="    Parse Tree    ", command=lambda: create_new_window1(entry),bg='LightGreen')
   # button5.pack(side='bottom')

   # validate string input using stack-buffer concept
   if sample_input_string != None:
      validity = validateStringUsingStackBuffer(parsing_table, result,
                                                tabTerm, sample_input_string,
                                                term_userdef, start_symbol, returned_tokenList)
      st = open('stack.txt', 'r')
      r = st.read()
      st.close()

      if "Invalid String!" in r:
         error1 = tk.Label(root,text= "The input is Invalid!")
         error1.pack()
         # button5.place_forget()
         # button6.place_forget()
      else:
         button6.place(x=130,y=10)
         button5.place(x=30,y=10)

   else:
      print("\nNo input String detected")

   Radiobutton(root, text="New Entry", command=lambda: hide_me(root,button6,button5)).place(x=250, y=10)


def create_new_window1(entry):
   # window2 = tk.Toplevel()
   # canvas2 = Canvas(window2, width=500, height=500)
   # # label = tk.Label(self.window2, text="This is window #%s" % self.count)
   # canvas2.pack(side="top", fill="both", expand=True, padx=40, pady=40)
   sample_input_string = entry

   tokenList = sample_input_string

   scannedTokens = tokenList.split('\n')
   Source_Code = []
   for line in scannedTokens:
      Source_Code.append(line)
      divText(Source_Code)

   returned_tokenList = divText(Source_Code)

   # validate string input using stack-buffer concept
   if sample_input_string != None:
      validity = validateStringUsingStackBuffer1(parsing_table, result,
                                                tabTerm, sample_input_string,
                                                term_userdef, start_symbol, returned_tokenList)
      print(validity)

      # label41 = tk.Label(canvas2,text=validity,anchor='w',justify=LEFT)
      # label41.pack()
   else:
      print("\nNo input String detected")

# bottomFrame = Frame(root)
# bottomFrame.pack(side=BOTTOM,fill=BOTH)
#
# myscrollbar = Scrollbar(bottomFrame, orient="vertical")
# myscrollbar.pack(side="right", fill="y")

def onClick(sample_input_string):

   tokenList = sample_input_string

   scannedTokens = tokenList.split('\n')
   Source_Code = []
   for line in scannedTokens:
      Source_Code.append(line)
      divText(Source_Code)

   label4 = tk.Label(root, text=str(divText(Source_Code)))
   label4.pack()

   for i in range(0,len(sample_input_string)):
      if (sample_input_string[i] == '/' and sample_input_string[i+1]== '0'):
         errorr = tk.Label(root,text= "The input string's syntax is accepted but note that it contains a mathematical error which is DIV/0")
         errorr.pack()

   returned_tokenList = divText(Source_Code)
   if "INVALIDID" in returned_tokenList:
      error = tk.Label(root,text= "The input contains an invalid ID")
      error.pack()
   # Radiobutton(root, text="clear", command=lambda: restart(root)).place(x=650, y=10)


def onClick1(sample_input_string):
   tokenList = sample_input_string
   scannedTokens = tokenList.split('\n')
   Source_Code = []
   for line in scannedTokens:
      Source_Code.append(line)
      divText1(Source_Code)


class NewWindow(Toplevel):

   def __init__(self, master=None):
      super().__init__(master=master,background="#E0E0E0")
      self.title("First and Follow Table")
      self.geometry("830x300")
      label = Label(self, text=str(ff), font=("Courier", 13),background="#E0E0E0")
      label.pack()

class showStackTable(Toplevel):
   def __init__(self, master=None):
      super().__init__(master=master)
      self.title("Stack and Action Table")
      self.geometry("1530x500")
      st = open('stack.txt', 'r')
      r = st.read()
      st.close()
      # label = Label(self, text=r, font=("Courier", 13))
      # label.pack()
      scroll = tk.Scrollbar(self, orient=HORIZONTAL)
      scroll.pack(side=BOTTOM, fill=X)
      v = Scrollbar(self)
      v.pack(side=RIGHT, fill=Y)
      text = Text(self, wrap=NONE, xscrollcommand=scroll.set,yscrollcommand=v.set)
      text.insert(END, r)
      text.pack(side=TOP, fill=X)
      labelfont = ('Courier', 13)
      text.config(font=labelfont)

      scroll.config(command=text.xview)
      v.config(command=text.yview)

class RulesWindow(Toplevel):

   def __init__(self, master=None):
      super().__init__(master=master,background="#E0E0E0")
      self.title("Case One Rules")
      self.geometry("1130x300")

      frame2 = Frame(self, width=300, height=320,background="#E0E0E0")
      # frame2.grid(row=0,column=0,sticky="ns")
      frame2.pack_propagate(0)
      frame2.pack(side='left',padx=10,pady=5)

      frame3 = Frame(self, width=300, height=320,background="#E0E0E0")
      frame3.pack_propagate(0)
      frame3.pack(side='left',padx=70,pady=5)

      frame4 = Frame(self, width=300, height=320,background="#E0E0E0")
      frame4.pack_propagate(0)
      frame4.pack( side='left',padx=50,pady=5)

      label7a = tk.Label(frame2, text="Rules :", justify=LEFT, font=LARGE_FONT,background="#E0E0E0")
      label7a.pack(anchor="w",pady=20)

      label7b = tk.Label(frame2, text="exp -> exp addop term | term", anchor='e', justify=LEFT, font=LARGE_FONT,background="#E0E0E0")
      label7b.pack(anchor="w",pady=5)

      label7c = tk.Label(frame2, text="addop -> + | -", anchor='e', justify=LEFT, font=LARGE_FONT,background="#E0E0E0")
      label7c.pack(anchor="w",pady=5)

      label7d = tk.Label(frame2, text="term -> term mullop factor | factor", anchor='e', justify=LEFT, font=LARGE_FONT,background="#E0E0E0")
      label7d.pack(anchor="w",pady=5)

      label7e = tk.Label(frame2, text="mullop -> * | /", anchor='e', justify=LEFT, font=LARGE_FONT,background="#E0E0E0")
      label7e.pack(anchor="w",pady=5)

      label7f = tk.Label(frame2, text="factor -> ( exp ) | Identifier | Number", anchor='e', justify=LEFT,
                         font=LARGE_FONT,background="#E0E0E0")
      label7f.pack(anchor="w",pady=5)

      ################################

      label8 = tk.Label(frame3, text="After elimination of left recursion: ", anchor='n', justify=LEFT, font=LARGE_FONT,background="#E0E0E0")
      label8.pack(anchor="w",pady=20)

      label8a = tk.Label(frame3, text="exp-> term exp' ", anchor='n', justify=LEFT, font=LARGE_FONT,background="#E0E0E0")
      label8a.pack(anchor="w",pady=5)

      label8b = tk.Label(frame3, text="exp'-> addop term exp' | \u03B5", anchor='n', justify=LEFT, font=LARGE_FONT,background="#E0E0E0")
      label8b.pack(anchor="w",pady=5)

      label8c = tk.Label(frame3, text="addop-> + | - ", anchor='n', justify=LEFT, font=LARGE_FONT,background="#E0E0E0")
      label8c.pack(anchor="w",pady=5)

      label8d = tk.Label(frame3, text="term-> factor term'", anchor='n', justify=LEFT, font=LARGE_FONT,background="#E0E0E0")
      label8d.pack(anchor="w",pady=5)

      label8e = tk.Label(frame3, text="term'-> mullop factor term' | \u03B5", anchor='n', justify=LEFT, font=LARGE_FONT,background="#E0E0E0")
      label8e.pack(anchor="w",pady=5)

      label8f = tk.Label(frame3, text="mullop-> * | /", anchor='n', justify=LEFT, font=LARGE_FONT,background="#E0E0E0")
      label8f.pack(anchor="w",pady=5)

      label8g = tk.Label(frame3, text="factor-> ( exp ) | Identifier | Number", anchor='n', justify=LEFT,
                         font=LARGE_FONT,background="#E0E0E0")
      label8g.pack(anchor="w",pady=5)

      ############################


      label9 = tk.Label(frame4, text="After left factoring:", anchor='n',justify=LEFT,font=LARGE_FONT,background="#E0E0E0")
      label9.pack(anchor="w",pady=20)

      label9a = tk.Label(frame4, text="exp-> term exp' ", anchor='n', justify=LEFT,font=LARGE_FONT,background="#E0E0E0")
      label9a.pack(anchor="w",pady=5)

      label9b = tk.Label(frame4, text="exp'-> addop term exp' | \u03B5", anchor='n', justify=LEFT,font=LARGE_FONT,background="#E0E0E0")
      label9b.pack(anchor="w",pady=5)

      label9c = tk.Label(frame4, text="addop-> + | - ", anchor='n', justify=LEFT,font=LARGE_FONT,background="#E0E0E0")
      label9c.pack(anchor="w",pady=5)

      label9d = tk.Label(frame4, text="term-> factor term'", anchor='n', justify=LEFT,font=LARGE_FONT,background="#E0E0E0")
      label9d.pack(anchor="w",pady=5)

      label9e = tk.Label(frame4, text="term'-> mullop factor term' | \u03B5", anchor='n', justify=LEFT,font=LARGE_FONT,background="#E0E0E0")
      label9e.pack(anchor="w",pady=5)

      label9f = tk.Label(frame4, text="mullop-> * | /", anchor='n', justify=LEFT,font=LARGE_FONT,background="#E0E0E0")
      label9f.pack(anchor="w",pady=5)

      label9g = tk.Label(frame4, text="factor-> ( exp ) | Identifier | Number", anchor='n', justify=LEFT,font=LARGE_FONT,background="#E0E0E0")
      label9g.pack(anchor="w",pady=5)



#############################################################################################################
LARGE_FONT = ("verdana", 10)

class SeaofBTCapp(tk.Tk):
   def __init__(self, *args, **kwargs):
      tk.Tk.__init__(self, *args, **kwargs)

      tk.Tk.wm_title(self, "Syntax Analyzer")
      tk.Tk.wm_minsize(self, 50, 50)

      container = tk.Frame(self)
      container.pack(side="top", fill="both", expand=True)

      container.grid_rowconfigure(0, weight=1)
      container.grid_columnconfigure(0, weight=1)

      self.frames = {}

      for F in (StartPage, PageOne):
         frame = F(container, self)
         self.frames[F] = frame
         frame.grid(row=0, column=0, sticky="new")
      self.show_frame(StartPage)

      def present():
         self.show_frame(StartPage)

   def show_frame(self, cont):
      frame = self.frames[cont]
      frame.tkraise()


class StartPage(tk.Frame):
   def __init__(self, parent, controller):
      tk.Frame.__init__(self, parent)

      # def temp_text(e):
      #    E.delete(0, "end")

      self.grid_rowconfigure(1, weight=1)
      self.grid_columnconfigure(0, weight=1)

      entryFrame = Frame(self, width=300, height=550,pady=3)
      entryFrame.grid(row = 0 , sticky="ew")

      centerFrame = Frame(self,width=300, height=155, padx=3, pady=30)
      centerFrame.grid(row=1,sticky="nsew")

      centerFrame.grid_rowconfigure(0, weight=1)
      centerFrame.grid_columnconfigure(1, weight=1)

      frame2 = Frame(centerFrame, width=100, height=55)
      frame3 = Frame(centerFrame,  width=100, height=55, padx=3, pady=3)
      frame4 = Frame(centerFrame,  width=100, height=55, padx=3, pady=3)

      frame2.grid(row=0, column=0, sticky="n")
      frame3.grid(row=0, column=1, sticky="n")
      frame4.grid(row=0, column=2, sticky="n")

      E = tk.Entry(entryFrame, width=50, borderwidth=5)
      # E.insert(0, "Enter Arithmetic Equation")
      E.bind("<FocusIn>")
      E.pack(ipady=5)

      Radiobutton(self, text="Update Stack", command=lambda: create_new_window(E.get())).place(x=840,y=10)

      global defineInputButton,ffButton,ptButton,stButton,rButton

      defineInputButton = tk.PhotoImage(file='DefineInputButton.png')
      button1 = tk.Button(entryFrame, text="Define Input", image=defineInputButton,command=lambda :onClick(E.get()),borderwidth=0)
      button1.image=defineInputButton
      button1.pack(padx=5,side=LEFT,pady=3)

      ffButton = tk.PhotoImage(file='ff.png')
      button2 = tk.Button(entryFrame, text=" First & Follow",image=ffButton,borderwidth=0)
      button2.bind("<Button>", lambda e: NewWindow(self))
      button2.image = ffButton
      button2.pack(padx=5,side=LEFT,pady=3)

      ptButton = tk.PhotoImage(file='pt.png')
      button3 = tk.Button(entryFrame, text="   Parse Table   ",image=ptButton, command=lambda: controller.show_frame(PageOne),borderwidth=0)
      button3.image = ptButton
      button3.pack(side=LEFT,padx= 5,pady=3)

      stButton = tk.PhotoImage(file='st.png')
      button4 = tk.Button(entryFrame, text="   Stack Table   ",image=stButton,borderwidth=0)
      button4.bind("<Button>", lambda e: showStackTable(self))
      button4.image = stButton
      button4.pack(side=LEFT,pady= 3,padx=5)

      rButton = tk.PhotoImage(file='r.png')
      button55 = tk.Button(frame3, text="Rules", image=rButton, borderwidth=0)
      button55.bind("<Button>", lambda e: RulesWindow(self))
      button55.image = rButton
      button55.pack(side="top", pady=4)

      global entry
      entry = E.get()





class PageOne(tk.Frame):
   def __init__(self, parent, controller):
      tk.Frame.__init__(self, parent)
      label = tk.Label(self, text="Parse Table", font=LARGE_FONT)
      label.pack(pady=10, padx=10)

      button1 = tk.Button(self, text="Back", command=lambda: controller.show_frame(StartPage))
      button1.pack()

      scroll = tk.Scrollbar(self, orient=HORIZONTAL)
      scroll.pack(side=BOTTOM, fill=X)

      # label44 = tk.Label(self, text=t,font=("Lucida Console", 7))
      # label44.pack()

      text = Text(self, wrap=NONE,xscrollcommand=scroll.set,height=11)
      text.insert(END, t)
      text.pack(side=TOP, fill=X)
      labelfont = ('Courier', 15)
      text.config(font=labelfont)

      scroll.config(command=text.xview)


x=0
s=0
q=0
listVar2=0
listVar1=0
listVar=0
counter=0
f=False
f2=False
f3=False
Flag=False
Flag1=True
ColorFlag=False
list1=[]
list2=[]
list3=[]
list4=[]
list5=[]
list6=[]
terminalsList=[]
def ParseTree(entry):
   global x,s,q,list1,list2,list3,list4,list5,list6,f,f2,f3,listVar,listVar1,listVar2,counter,Flag,Flag1,terminalsList
   if(entry=="Valid"):
      net.show("ParseTree.html")
   else:
      temp = entry.split("->")
      list1.append(temp[0])

      if(len(list2)==0):
         if(len(list1)==1):
            net.add_node(temp[0],color='Red')

         else:
            net.add_node(temp[0])
      else:

         for v in range(0,len(list2)):
            if(temp[0]!=list2[v]):
               net.add_node(temp[0])
            else:
              r= list3[v]
              listVar = v
              f2=True
              break
         if(f2==False):
            for g in range(0,len(list6)):
               if (temp[0] != list6[g]):
                  net.add_node(temp[0])
               else:
                  listVar2 = list5[g]
                  listVar1 = g
                  f3 = True
                  break

      for i in range(1,len(temp)):
         children = temp[i].split(" ")

         for j in range(0,len(children)):
            for k in range(0, len(list1)):
               if (children[j]==list1[k]):

                  list2.append(children[j])
                  s = x + 1
                  list3.append(s)
                  x=s+1
                  net.add_node(s, children[j])
                  if(f2==True):
                     net.add_edge(r, s)
                  elif(f3==True):
                     net.add_edge(listVar2, s)
                  else:
                     net.add_edge(temp[0], s)

                  f=True
                  Flag1=False
                  break
            if(Flag1==True):
               for d in range(0,len(list4)):
                  if (children[j]==list4[d]):
                     q = x + 1
                     net.add_node(q,children[j])
                     list5.append(q)
                     list6.append(children[j])
                     x=q+1
                     if (f2 == True):
                        net.add_edge(r, q)
                     else:
                        net.add_edge(temp[0], q)
                     f = True
                     break

            if(f==False):
               if(children[j]=="Number" or children[j]=="#" or children[j]=="Identifier" or children[j]=="-" or children[j]=="+" or children[j]=="*" or children[j]=="/" or children[j]==")" or children[j]=="("):
                  terminalsList.append(children[j])
                  net.add_node(x,children[j])
                  if (f2 == True):
                     net.add_edge(r, x)
                  elif(f3== True):
                     net.add_edge(listVar2, x)
                  else:
                     net.add_edge(temp[0], x)
                  x=x+1

               else:
                  list4.append(children[j])
                  for h in range(0,len(list4)-1):
                     if(children[j]==list4[h]):
                        q=x+1
                        net.add_node(q,children[j])
                        list5.append(q)
                        list6.append(children[j])
                        x=x+1
                  net.add_node(children[j])
                  if (f2 == True):
                     net.add_edge(r, children[j])
                  elif (f3 == True):
                     net.add_edge(listVar2, children[j])
                  else:
                     net.add_edge(temp[0],children[j])

            f=False
            Flag1=True
         if(f2==True):
            list2[listVar] = 0
            list3[listVar] = 0
         f2 = False
         if (f3 == True):
            list6[listVar1] = 0
            list5[listVar1] = 0
         f3 = False

root = SeaofBTCapp()
root.mainloop()
#############################################################################################################

