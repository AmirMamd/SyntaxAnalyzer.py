from tkinter import *
from tkinter import ttk
# Import tkinter library
from tkinter import *
from tkinter import ttk
import matplotlib
import networkx as nx
import matplotlib.pyplot as plt

matplotlib.use("TKAgg")
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg, NavigationToolbar2Tk as NavigationToolbar2TkAgg
from matplotlib.figure import Figure
import tkinter as tk
import nltk
import re
from automata.fa.dfa import DFA


class Lexer:
    def init(self):
        pass

    def divText(self, Source_Code):
        patternID = r"(^[^\d\W]\w*\Z)"  # for Identifier
        patternNum = r"[0.0-9.9]+"  # for NUM and Decimals
        patternOP = r"[+\-\*\/]"
        patternParenthesis1 = r"[\(]"
        patternParenthesis2 = r"[\)]"

        for line in Source_Code:
            tokenList = nltk.wordpunct_tokenize(line)
            print(tokenList)

        num = p1 = p2 = op = 0
        for i in range(0, len(tokenList)):
            count = 0
            print(tokenList[i])
            if (tokenList[i] == '/' and tokenList[i + 1] == '0'):
                # print("Invalid divide!")
                label1 = Label(root, text="Invalid divide! going to Error State")
                label1.pack()
                break
            if re.fullmatch(patternID, tokenList[i]):
                # print("Match ID!")
                count = 1
                label2 = Label(root, text=tokenList[i] + " : Identifier ")
                label2.pack()
                num = num + 1
            else:
                print("Not a match ID!")
            if re.fullmatch(patternNum, tokenList[i]):
                # print("Match Num!")
                count = 1
                label3 = Label(root, text=tokenList[i] + " : Number ")
                label3.pack()
                num = num + 1
            else:
                print("Not a match Num!")
            if re.fullmatch(patternOP, tokenList[i]):
                # print("Match op!")
                count = 1
                label4 = Label(root, text=tokenList[i] + " : Operator ")
                label4.pack()
                op = op + 1
            else:
                print("Not a match op!")
            if re.fullmatch(patternParenthesis1, tokenList[i]):
                # print("Match Parenthesis!")
                count = 1
                label5 = Label(root, text=tokenList[i] + " : Open Bracket ")
                label5.pack()
                p1 = p1 + 1
            else:
                print("Not a match Open Parenthesis!")
            if re.fullmatch(patternParenthesis2, tokenList[i]):
                # print("Match Parenthesis!")
                count = 1
                label6 = Label(root, text=tokenList[i] + " : Close Bracket ")
                label6.pack()
                p2 = p2 + 1
            else:
                print("Not a match Close Parenthesis!")
            if(count == 0):
                label15 = Label(root,text= tokenList[i] + ": Don't match any of the regular expressions")
                label15.pack()
        if ((num - op) == 1 and op != 0):
            pass
        else:
            # print("missing operator")
            label7 = Label(root, text=" Missing or Extra Operators")
            label7.pack()
        if (p1 != p2):
            # print("missing parenthesis")
            label8 = Label(root, text=" Missing or Extra parenthesis")
            label8.pack()
        #     //////////////////////////////////////////////////
        tokenType = ["" for x in range(len(tokenList))]
        for i in range(0, len(tokenList)):
            if (tokenList[i] == '-'):
                tokenType[i] = 'MINUS'
            else:
                if (tokenList[i] == '+'):
                    tokenType[i] = 'PLUS'
                else:
                    if (tokenList[i] == '/'):
                        tokenType[i] = 'DIV'
                    else:
                        if (tokenList[i] == '*'):
                            tokenType[i] = 'MULT'
                        else:
                            if re.fullmatch(patternID, tokenList[i]):
                                tokenType[i] = 'IDENTIFIER'
                            else:
                                if (re.fullmatch(patternNum, tokenList[i])):  # and this num is not 0 then NUMBER[1-9],If it was 0 then '0'
                                    if (tokenList[i] == '0'):
                                        tokenType[i] = '0'
                                    else:
                                        tokenType[i] = 'NUMBER[1-9]'
                                else:
                                    if re.fullmatch(patternParenthesis1, tokenList[i]):
                                        tokenType[i] = 'OPENBRACKET'
                                    else:
                                        if re.fullmatch(patternParenthesis2, tokenList[i]):
                                            tokenType[i] = 'CLOSEBRACKET'
                                        else:
                                            tokenType[i] = 'INVALIDID'
        # ///////////////////////////////////////////////////////////////

        dfa = DFA(
            states={'1', '2', 'ID1', 'ID2', 'NUM1', 'NUM2', 'OP1', 'OP2', 'OP3', 'OP4', '3', 'ID3', 'ID4', 'NUM3',
                    'NUM4', 'X'},
            input_symbols={'IDENTIFIER', 'PLUS', 'MINUS', 'MULT', 'DIV', 'OPENBRACKET', 'CLOSEBRACKET', 'NUMBER[1-9]',
                           '0','INVALIDID'},
            transitions={
                '1': {'IDENTIFIER': 'ID1', 'PLUS': 'X', 'MINUS': 'X', 'MULT': 'X', 'DIV': 'X', 'OPENBRACKET': '2',
                      'CLOSEBRACKET': 'X', 'NUMBER[1-9]': 'NUM1', '0': 'NUM1','INVALIDID':'X'},
                'ID1': {'IDENTIFIER': 'ID1', 'PLUS': 'OP1', 'MINUS': 'OP1', 'MULT': 'OP1', 'DIV': 'OP2',
                        'OPENBRACKET': 'X', 'CLOSEBRACKET': 'X', 'NUMBER[1-9]': 'ID1', '0': 'ID1','INVALIDID':'X'},
                'NUM1': {'IDENTIFIER': 'X', 'PLUS': 'OP1', 'MINUS': 'OP1', 'MULT': 'OP1', 'DIV': 'OP2',
                         'OPENBRACKET': 'X', 'CLOSEBRACKET': 'X', 'NUMBER[1-9]': 'NUM1', '0': 'NUM1','INVALIDID':'X'},
                'OP1': {'IDENTIFIER': 'ID3', 'PLUS': 'X', 'MINUS': 'X', 'MULT': 'X', 'DIV': 'X', 'OPENBRACKET': '2',
                        'CLOSEBRACKET': 'X', 'NUMBER[1-9]': 'NUM3', '0': 'NUM3','INVALIDID':'X'},
                'OP2': {'IDENTIFIER': 'ID3', 'PLUS': 'X', 'MINUS': 'X', 'MULT': 'X', 'DIV': 'X', 'OPENBRACKET': '2',
                        'CLOSEBRACKET': 'X', 'NUMBER[1-9]': 'NUM3', '0': 'X','INVALIDID':'X'},
                'ID3': {'IDENTIFIER': 'ID3', 'PLUS': 'OP1', 'MINUS': 'OP1', 'MULT': 'OP1', 'DIV': 'OP2',
                        'OPENBRACKET': 'X', 'CLOSEBRACKET': 'X', 'NUMBER[1-9]': 'ID3', '0': 'ID3','INVALIDID':'X'},
                'NUM3': {'IDENTIFIER': 'X', 'PLUS': 'OP1', 'MINUS': 'OP1', 'MULT': 'OP1', 'DIV': 'OP2',
                         'OPENBRACKET': 'X', 'CLOSEBRACKET': 'X', 'NUMBER[1-9]': 'NUM3', '0': 'NUM3','INVALIDID':'X'},
                '3': {'IDENTIFIER': 'X', 'PLUS': 'OP1', 'MINUS': 'OP1', 'MULT': 'OP1', 'DIV': 'OP2', 'OPENBRACKET': 'X',
                      'CLOSEBRACKET': 'X', 'NUMBER[1-9]': 'X', '0': 'X','INVALIDID':'X'},
                'X': {'IDENTIFIER': 'X', 'PLUS': 'X', 'MINUS': 'X', 'MULT': 'X', 'DIV': 'X', 'OPENBRACKET': 'X',
                      'CLOSEBRACKET': 'X', 'NUMBER[1-9]': 'X', '0': 'X','INVALIDID':'X'},
                '2': {'IDENTIFIER': 'ID2', 'PLUS': 'X', 'MINUS': 'X', 'MULT': 'X', 'DIV': 'X', 'OPENBRACKET': 'X',
                      'CLOSEBRACKET': 'X', 'NUMBER[1-9]': 'NUM2', '0': 'NUM2','INVALIDID':'X'},
                'ID2': {'IDENTIFIER': 'ID2', 'PLUS': 'OP3', 'MINUS': 'OP3', 'MULT': 'OP3', 'DIV': 'OP4',
                        'OPENBRACKET': 'X', 'CLOSEBRACKET': 'X', 'NUMBER[1-9]': 'ID2', '0': 'ID2','INVALIDID':'X'},
                'NUM2': {'IDENTIFIER': 'X', 'PLUS': 'OP3', 'MINUS': 'OP3', 'MULT': 'OP3', 'DIV': 'OP4',
                         'OPENBRACKET': 'X', 'CLOSEBRACKET': 'X', 'NUMBER[1-9]': 'NUM2', '0': 'NUM2','INVALIDID':'X'},
                'OP3': {'IDENTIFIER': 'ID4', 'PLUS': 'X', 'MINUS': 'X', 'MULT': 'X', 'DIV': 'X', 'OPENBRACKET': 'X',
                        'CLOSEBRACKET': 'X', 'NUMBER[1-9]': 'NUM4', '0': 'NUM4','INVALIDID':'X'},
                'OP4': {'IDENTIFIER': 'ID4', 'PLUS': 'X', 'MINUS': 'X', 'MULT': 'X', 'DIV': 'X', 'OPENBRACKET': 'X',
                        'CLOSEBRACKET': 'X', 'NUMBER[1-9]': 'NUM4', '0': 'X','INVALIDID':'X'},
                'ID4': {'IDENTIFIER': 'ID4', 'PLUS': 'OP3', 'MINUS': 'OP3', 'MULT': 'OP3', 'DIV': 'OP4',
                        'OPENBRACKET': 'X', 'CLOSEBRACKET': '3', 'NUMBER[1-9]': 'ID4', '0': 'ID4','INVALIDID':'X'},
                'NUM4': {'IDENTIFIER': 'X', 'PLUS': 'OP3', 'MINUS': 'OP3', 'MULT': 'OP3', 'DIV': 'OP4',
                         'OPENBRACKET': 'X', 'CLOSEBRACKET': '3', 'NUMBER[1-9]': 'NUM4', '0': 'NUM4','INVALIDID':'X'}

            },
            initial_state='1',
            #final_states={'ID3', 'NUM3', '3'}
            final_states={'1', '2', 'ID1', 'ID2', 'NUM1', 'NUM2', 'OP1', 'OP2', 'OP3', 'OP4', '3', 'ID3', 'ID4', 'NUM3',
                    'NUM4', 'X'}
        )
        if (str(dfa.read_input(tokenType)) == 'ID3'):
            label100 = Label(root, text= "Input Accepted")
            label100.pack()
            label11 = Label(root, text="Final State : " + str(dfa.read_input(tokenType)))
            label11.pack()
            print("Accepted")
        else:
            if (str(dfa.read_input(tokenType)) == '3'):
                label99 = Label(root, text="Input Accepted")
                label99.pack()
                label95 = Label(root, text="Final State : " + str(dfa.read_input(tokenType)))
                label95.pack()
                print("Accepted")
                print("Final State : " + str(dfa.read_input(tokenType)))
            else:
                if (str(dfa.read_input(tokenType)) == 'NUM3'):
                    label98 = Label(root, text="Input Accepted")
                    label98.pack()

                    label94 = Label(root, text="Final State : " + str(dfa.read_input(tokenType)))
                    label94.pack()
                    print("Accepted")
                    print("Final State : " + str(dfa.read_input(tokenType)))
                else:
                    print("Rejected, the DFA stopped on a non-final state  " + str(dfa.read_input(tokenType)))
                    label97 = Label(root, text="Rejected, the DFA stopped on a non-final state  " + str(dfa.read_input(tokenType)))
                    label97.pack()
        states_list = (list(dfa.read_input_stepwise(tokenType)))
        print("Tokens : ", tokenType)
        print("State Sequence : ", states_list)
        # if dfa.accepts_input(tokenType):
        #         print('\nAccepted')
        #         label9 = Label(root, text="Input is: Accepted")
        #         label9.pack()
        # else:
        #     label10 = Label(root, text="Rejected, the DFA stopped on a non-final state")
        #     label10.pack()
        #     #dfa._check_for_input_rejection(str(dfa.read_input(tokenType)))
        #     print('Rejected, the DFA stopped on a non-final state')
        #
        # print("Final State : " + str(dfa.read_input(tokenType)))
        # states_list = (list(dfa.read_input_stepwise(tokenType)))
        # print("Tokens : ", tokenType)
        # print("State Sequence : ", states_list)
        #
        # label11 = Label(root, text="Final State : " + str(dfa.read_input(tokenType)))
        # label11.pack()
        label12 = Label(root, text="Tokens : " + str(tokenType))
        label12.pack()
        label13 = Label(root, text="State Sequence :" + str(states_list))
        label13.pack()

        # //////////////////////////////////////////////////////////////////////////////

    def remove_Spaces(self, program):
        scanned_Program = []
        for line in program:
            if (line.strip() != ''):
                scanned_Program.append(line.strip())
        return scanned_Program

    def exc(self, text):
        scanned_Prog = self.remove_Spaces(text)
        scanned_Program_lines = text.split('\n')
        Source_Code = []
        for line in scanned_Program_lines:
            Source_Code.append(line)
            self.divText(Source_Code)


root = Tk()
root.minsize(400, 400)
root.title('Simple Compiler')
label1 = Label(root, text="Welcome to our first Compiler")
label1.pack()


def temp_text(e):
    E.delete(0, "end")


E = Entry(root, width=50, borderwidth=5)
E.insert(0, "Enter Arithmetic Equation")
E.bind("<FocusIn>", temp_text)

E.pack()

def onClick():
    showDFAButton.pack()
    l1 = Lexer()
    LabelID = Label(root,text = "Identifier: "+ "(^[^\d\W]\w*\Z)")
    LabelNum = Label(root, text= "Number: "+"[0.0-9.9]+")
    LabelOp = Label(root, text= "Operators: "+ "[+\-\*\/]")
    LabelP1 = Label(root, text = "Open Brackets: "+"[\(]")
    LabelP2 = Label(root, text="Closed Brackets: "+"[\)]")
    LabelID.pack()
    LabelNum.pack()
    LabelOp.pack()
    LabelP1.pack()
    LabelP2.pack()
    l1.exc(E.get())
    # l1.trace()



# ////////////
def open_win():
    LARGE_FONT = ("verdana", 12)

    class SeaofBTCapp(tk.Tk):
        def __init__(self, *args, **kwargs):
            tk.Tk.__init__(self, *args, **kwargs)

            tk.Tk.wm_title(self, "Case 1 DFA")
            tk.Tk.wm_minsize(self, 800, 300)

            container = tk.Frame(self)
            container.pack(side="top", fill="both", expand=True)

            container.grid_rowconfigure(0, weight=1)
            container.grid_columnconfigure(0, weight=1)

            self.frames = {}

            for F in (StartPage, PageOne, PageTwo, PageThree):
                frame = F(container, self)
                self.frames[F] = frame
                frame.grid(row=0, column=0, sticky="nsew")
            self.show_frame(StartPage)

            def present():
                self.show_frame(StartPage)

        def show_frame(self, cont):
            frame = self.frames[cont]
            frame.tkraise()

    class StartPage(tk.Frame):
        def __init__(self, parent, controller):
            tk.Frame.__init__(self, parent)
            label = tk.Label(self, text="DFA", font=LARGE_FONT)
            label.pack(pady=10, padx=10)

            button1 = tk.Button(self, text="View node ID1", command=lambda: controller.show_frame(PageOne))
            button1.pack()

            button2 = tk.Button(self, text="View node NUM1", command=lambda: controller.show_frame(PageTwo))
            button2.pack()

            button3 = tk.Button(self, text="View node B", command=lambda: controller.show_frame(PageThree))
            button3.pack()

            f = Figure(figsize=(5, 5), dpi=100)
            a = f.add_subplot(111)

            G = nx.DiGraph()

            G.add_node(' ')
            G.add_node('X')
            G.add_node('other')
            G.add_node('+,-,*,/')
            G.add_node(' +,-,*,/,other')
            G.add_node('+,-,*,/,0 ')
            G.add_node('/')
            G.add_node(' /')
            G.add_node('+,-,*')
            G.add_node('+,-,* ')
            G.add_edges_from([(' ', 1)])

            transition = [(1, 'ID1', 'L or _'), (1, 'NUM1', '0-9'), (1, 'B', '('), ('ID1', 'OP1', '+,-,*'),
                          ('ID1', 'OP2', '/'), ('NUM1', 'OP1', '+,-,*'), ('NUM1', 'OP2', '/'), ('OP1', 'NUM3', '0-9'),
                          ('OP1', 'ID3', 'L or _'), ('OP2', 'ID3', 'L or _'), ('OP2', 'NUM3', '1-9'), ('B', 3, ')'),
                          ('OP1', 'B', '('), ('OP2', 'B', '('), (3, 'OP1', '+,-,*'), (3, 'OP2', '/'),
                          ('X', 'X', 'other')]
            for i in transition:
                G.add_edge(i[0], i[1], transition=i[2])

            positions = {'X': [-3, -6], 'ID1': [-2, -2], 'NUM1': [-2, -4], 'OP1': [0, -2], 'OP2': [0, -4],
                         'NUM3': [3, -4],
                         'ID3': [3, -2], 'B': [-2, -6], 3: [1, -6], ' ': [-5.1, -4], 1: [-4, -4], 'other': [-1, -6.9],
                         '+,-,*,/': [-3.6, -5.5], ' +,-,*,/,other': [-2.3, -3], '+,-,*,/,0 ': [-2.2, -4.7],
                         ' /': [1.5, -4.3],
                         '/': [2.8, -2.5], '+,-,*': [1.8, -1.7], '+,-,* ': [2.7, -3.4]}

            fixed_nodes = positions.keys()
            pos = nx.spring_layout(G, pos=positions, fixed=fixed_nodes)

            nx.draw(G, pos, with_labels=True, font_size=8, node_size=400, node_color='LightGreen', node_shape='o', ax=a)
            nx.draw_networkx_nodes(G, pos, node_size=500, node_color='w', node_shape='o', nodelist=[(' ')], ax=a)
            nx.draw_networkx_nodes(G, pos, node_size=500, node_color='w', node_shape='o', nodelist=[('other')], ax=a)
            nx.draw_networkx_nodes(G, pos, node_size=500, node_color='w', node_shape='o', nodelist=[('+,-,*,/')], ax=a)
            nx.draw_networkx_nodes(G, pos, node_size=500, node_color='w', node_shape='o', nodelist=[(' +,-,*,/,other')],
                                   ax=a)
            nx.draw_networkx_nodes(G, pos, node_size=500, node_color='w', node_shape='o', nodelist=[('+,-,*,/,0 ')],
                                   ax=a)

            nx.draw_networkx_nodes(G, pos, node_size=500, node_color='w', node_shape='o', nodelist=[('+,-,* ')], ax=a)
            nx.draw_networkx_nodes(G, pos, node_size=500, node_color='w', node_shape='o', nodelist=[('+,-,*')], ax=a)
            nx.draw_networkx_nodes(G, pos, node_size=500, node_color='w', node_shape='o', nodelist=[(' /')], ax=a)
            nx.draw_networkx_nodes(G, pos, node_size=500, node_color='w', node_shape='o', nodelist=[('/')], ax=a)

            nx.draw_networkx_edges(G, pos, edge_color='LightGreen', edgelist=[('OP1', 'B')], width=1, arrowsize=14,
                                   ax=a)
            nx.draw_networkx_edges(G, pos, edge_color='LightGreen', edgelist=[('OP2', 'B')], width=1, arrowsize=14,
                                   ax=a)
            nx.draw_networkx_edges(G, pos, edge_color='LightGreen', edgelist=[(3, 'OP1')], width=1, arrowsize=14, ax=a)
            nx.draw_networkx_edges(G, pos, edge_color='LightGreen', edgelist=[(3, 'OP2')], width=1, arrowsize=14, ax=a)
            # nx.draw_networkx_edges(G,pos,edge_color='g',edgelist = [(' ',1)] , width=1,arrowsize=14)

            nx.draw_networkx_nodes(G, pos, node_size=200, node_color='LightGreen', node_shape='o', nodelist=[(3)],
                                   edgecolors='black', ax=a)
            nx.draw_networkx_nodes(G, pos, node_size=200, node_color='LightGreen', node_shape='o', nodelist=[('ID3')],
                                   edgecolors='black', ax=a)
            nx.draw_networkx_nodes(G, pos, node_size=200, node_color='LightGreen', node_shape='o', nodelist=[('NUM3')],
                                   edgecolors='black', ax=a)

            nx.draw_networkx_edge_labels(G, pos, edge_labels=nx.get_edge_attributes(G, 'transition'), label_pos=0.7,
                                         font_size=8, ax=a)
            nx.draw_networkx_edges(G, pos, edge_color='r', connectionstyle='arc3, rad = 0.3', edgelist=[(1, 'X')],
                                   width=1,
                                   arrowsize=9, ax=a)
            nx.draw_networkx_edges(G, pos, edge_color='r', connectionstyle='arc3, rad = 0.5', edgelist=[('OP1', 'X')],
                                   width=1, arrowsize=9, ax=a)
            nx.draw_networkx_edges(G, pos, edge_color='r', connectionstyle='arc3, rad = 0.4', edgelist=[('OP2', 'X')],
                                   width=1, arrowsize=9, ax=a)
            nx.draw_networkx_edges(G, pos, edge_color='r', connectionstyle='arc3, rad = -0.5', edgelist=[(3, 'X')],
                                   width=1,
                                   arrowsize=9, ax=a)
            nx.draw_networkx_edges(G, pos, edge_color='b', connectionstyle='arc3, rad = 0.3',
                                   edgelist=[('NUM3', 'OP1')],
                                   width=1, arrowsize=9, ax=a)
            nx.draw_networkx_edges(G, pos, edge_color='b', connectionstyle='arc3, rad = -0.3',
                                   edgelist=[('NUM3', 'OP2')],
                                   width=1, arrowsize=9, ax=a)
            nx.draw_networkx_edges(G, pos, edge_color='b', connectionstyle='arc3, rad = 0.3', edgelist=[('ID3', 'OP1')],
                                   width=1, arrowsize=9, ax=a)
            nx.draw_networkx_edges(G, pos, edge_color='b', connectionstyle='arc3, rad = -0.3',
                                   edgelist=[('ID3', 'OP2')],
                                   width=1, arrowsize=9, ax=a)

            canvas = FigureCanvasTkAgg(f, self)
            # canvas.show()
            canvas.draw()
            canvas.get_tk_widget().pack(side=tk.BOTTOM, fill=tk.BOTH, expand=True)

            toolbar = NavigationToolbar2TkAgg(canvas, self)
            toolbar.update()
            canvas._tkcanvas.pack(side=tk.TOP, fill=tk.BOTH, expand=True)

    class PageOne(tk.Frame):
        def __init__(self, parent, controller):
            tk.Frame.__init__(self, parent)
            label = tk.Label(self, text="Identifier DFA", font=LARGE_FONT)
            label.pack(pady=10, padx=10)

            button1 = tk.Button(self, text="Back to DFA", command=lambda: controller.show_frame(StartPage))
            button1.pack()

            f = Figure(figsize=(5, 5), dpi=100)
            a = f.add_subplot(111)

            ID = nx.DiGraph()
            ID.add_node('A-Z,a-z,_,0-9')
            ID.add_node(' ')
            ID.add_edges_from([('A', 'A'), (' ', 'A')])

            transition = [('A', 'X', ';'), ('A', 'OP1', '+,-,*'), ('A', 'OP2', '/'), ('X', 'X', 'other')]
            for i in transition:
                ID.add_edge(i[0], i[1], transition=i[2])

            positions = {'A': [0, 0], 'OP1': [1, 1], 'OP2': [1, -1], 'X': [0, -1], 'A-Z,a-z,_,0-9': [0, 0.3],
                         ' ': [-0.2, 0]}

            fixed_nodes = positions.keys()
            pos = nx.spring_layout(ID, pos=positions, fixed=fixed_nodes)

            nx.draw(ID, pos, with_labels=True, font_size=8, node_size=400, node_color='violet', node_shape='o', ax=a)
            nx.draw_networkx_nodes(ID, pos, node_size=500, node_color='w', node_shape='o', nodelist=[('A-Z,a-z,_,0-9')],
                                   ax=a)
            nx.draw_networkx_nodes(ID, pos, node_size=500, node_color='w', node_shape='o', nodelist=[(' ')], ax=a)
            nx.draw_networkx_nodes(ID, pos, node_size=200, node_color='violet', node_shape='o', nodelist=[('A')],
                                   edgecolors='black', ax=a)
            nx.draw_networkx_nodes(ID, pos, node_size=500, node_color='LightGreen', node_shape='o', nodelist=[('OP1')],
                                   ax=a)
            nx.draw_networkx_nodes(ID, pos, node_size=500, node_color='LightGreen', node_shape='o', nodelist=[('OP2')],
                                   ax=a)
            nx.draw_networkx_edges(ID, pos, edge_color='g', edgelist=[(' ', 'A')], width=1, arrowsize=14, ax=a)
            nx.draw_networkx_edges(ID, pos, edge_color='g', edgelist=[('A', 'OP1')], width=1, arrowsize=14, ax=a)
            nx.draw_networkx_edges(ID, pos, edge_color='g', edgelist=[('A', 'OP2')], width=1, arrowsize=14, ax=a)

            nx.draw_networkx_edge_labels(ID, pos, edge_labels=nx.get_edge_attributes(ID, 'transition'), label_pos=0.5,
                                         font_size=10, ax=a)
            canvas = FigureCanvasTkAgg(f, self)
            # canvas.show()
            canvas.draw()
            canvas.get_tk_widget().pack(side=tk.BOTTOM, fill=tk.BOTH, expand=True)

            toolbar = NavigationToolbar2TkAgg(canvas, self)
            toolbar.update()
            canvas._tkcanvas.pack(side=tk.TOP, fill=tk.BOTH, expand=True)

    class PageTwo(tk.Frame):
        def __init__(self, parent, controller):
            tk.Frame.__init__(self, parent)
            label = tk.Label(self, text="Num DFA", font=LARGE_FONT)
            label.pack(pady=10, padx=10)

            button1 = tk.Button(self, text="Back to DFA", command=lambda: controller.show_frame(StartPage))
            button1.pack()

            f = Figure(figsize=(5, 5), dpi=100)
            a = f.add_subplot(111)

            NUM = nx.DiGraph()
            NUM.add_node('0-9')
            NUM.add_node(' ')
            NUM.add_edges_from([('A', 'A'), (' ', 'A')])

            transition = [('A', 'X', '-[0-9]'), ('A', 'OP1', '+,-,*'), ('A', 'OP2', '/'), ('X', 'X', 'other')]
            for i in transition:
                NUM.add_edge(i[0], i[1], transition=i[2])

            positions = {'A': [0, 0], 'OP1': [1, 1], 'OP2': [1, -1], 'X': [0, -1], '0-9': [0, 0.3], ' ': [-0.2, 0]}

            fixed_nodes = positions.keys()
            pos = nx.spring_layout(NUM, pos=positions, fixed=fixed_nodes)

            nx.draw(NUM, pos, with_labels=True, font_size=9, node_size=400, node_color='orange', node_shape='o', ax=a)
            nx.draw_networkx_nodes(NUM, pos, node_size=500, node_color='w', node_shape='o', nodelist=[('0-9')], ax=a)
            nx.draw_networkx_nodes(NUM, pos, node_size=500, node_color='w', node_shape='o', nodelist=[(' ')], ax=a)
            nx.draw_networkx_nodes(NUM, pos, node_size=200, node_color='orange', node_shape='o', nodelist=[('A')],
                                   edgecolors='black', ax=a)
            nx.draw_networkx_nodes(NUM, pos, node_size=500, node_color='LightGreen', node_shape='o', nodelist=[('OP1')],
                                   ax=a)
            nx.draw_networkx_nodes(NUM, pos, node_size=500, node_color='LightGreen', node_shape='o', nodelist=[('OP2')],
                                   ax=a)
            nx.draw_networkx_edges(NUM, pos, edge_color='g', edgelist=[(' ', 'A')], width=1, arrowsize=14, ax=a)
            nx.draw_networkx_edges(NUM, pos, edge_color='g', edgelist=[('A', 'OP1')], width=1, arrowsize=14, ax=a)
            nx.draw_networkx_edges(NUM, pos, edge_color='g', edgelist=[('A', 'OP2')], width=1, arrowsize=14, ax=a)

            nx.draw_networkx_edge_labels(NUM, pos, edge_labels=nx.get_edge_attributes(NUM, 'transition'), label_pos=0.5,
                                         font_size=9, ax=a)

            canvas = FigureCanvasTkAgg(f, self)
            # canvas.show()
            canvas.draw()
            canvas.get_tk_widget().pack(side=tk.BOTTOM, fill=tk.BOTH, expand=True)

            toolbar = NavigationToolbar2TkAgg(canvas, self)
            toolbar.update()
            canvas._tkcanvas.pack(side=tk.TOP, fill=tk.BOTH, expand=True)

    class PageThree(tk.Frame):
        def __init__(self, parent, controller):
            tk.Frame.__init__(self, parent)
            label = tk.Label(self, text="Bracket DFA", font=LARGE_FONT)
            label.pack(pady=10, padx=10)

            button1 = tk.Button(self, text="Back to DFA", command=lambda: controller.show_frame(StartPage))
            button1.pack()

            f = Figure(figsize=(5, 5), dpi=100)
            a = f.add_subplot(111)

            B = nx.DiGraph()

            B.add_node(' ')
            B.add_node('X')
            # B.add_node('other')
            B.add_node('+,-,*,/')
            B.add_node(' +,-,*,/,0')  # from OP4
            B.add_node('+,-,*,/,other ')  # from OP3
            B.add_node('/')
            B.add_node(' /')  # from NUM4
            B.add_node('+,-,*')
            B.add_node('+,-,* ')  # from NUM4
            B.add_edges_from([(' ', 2)])

            transition = [(2, 'ID2', 'L or _'), (2, 'NUM2', '0-9'), ('ID2', 'OP3', '+,-,*'), ('ID2', 'OP4', '/'),
                          ('NUM2', 'OP3', '+,-,*'), ('NUM2', 'OP4', '/'), ('OP3', 'NUM4', '0-9'),
                          ('OP3', 'ID4', 'L or _'),
                          ('OP4', 'ID4', 'L or _'), ('OP4', 'NUM4', '1-9'), ('ID4', 3, ')'), ('NUM4', 3, ')'),
                          ('X', 'X', 'other')]
            for i in transition:
                B.add_edge(i[0], i[1], transition=i[2])

            positions = {'X': [-3, -6], 'ID2': [-2, -2], 'NUM2': [-2, -4], 'OP3': [0, -2], 'OP4': [0, -4],
                         'ID4': [3, -2],
                         'NUM4': [3, -4], 3: [4, -3], ' ': [-4.1, -3], 2: [-3, -3], 'OP1': [4, -2], 'OP2': [5, -2],
                         'other': [1, -5.5], '+,-,*,/': [-3.2, -5.5], ' +,-,*,/,0': [-0.2, -4.5],
                         '+,-,*,/,other ': [-1.2, -4.7],
                         ' /': [1.5, -4.3], '/': [2.8, -2.5], '+,-,*': [1.8, -1.7], '+,-,* ': [2.7, -3.4]}

            fixed_nodes = positions.keys()
            pos = nx.spring_layout(B, pos=positions, fixed=fixed_nodes)

            nx.draw(B, pos, with_labels=True, font_size=8, node_size=400, node_color='SkyBlue', node_shape='o', ax=a)
            nx.draw_networkx_nodes(B, pos, node_size=500, node_color='w', node_shape='o', nodelist=[(' ')], ax=a)
            # nx.draw_networkx_nodes(B, pos, node_size=500, node_color='w',node_shape='o',nodelist=[('other')])
            nx.draw_networkx_nodes(B, pos, node_size=500, node_color='w', node_shape='o', nodelist=[('+,-,*,/')], ax=a)
            nx.draw_networkx_nodes(B, pos, node_size=500, node_color='w', node_shape='o', nodelist=[(' +,-,*,/,0')],
                                   ax=a)
            nx.draw_networkx_nodes(B, pos, node_size=500, node_color='w', node_shape='o', nodelist=[('+,-,*,/,other ')],
                                   ax=a)

            nx.draw_networkx_nodes(B, pos, node_size=500, node_color='w', node_shape='o', nodelist=[('+,-,* ')], ax=a)
            nx.draw_networkx_nodes(B, pos, node_size=500, node_color='w', node_shape='o', nodelist=[('+,-,*')], ax=a)
            nx.draw_networkx_nodes(B, pos, node_size=500, node_color='w', node_shape='o', nodelist=[(' /')], ax=a)
            nx.draw_networkx_nodes(B, pos, node_size=500, node_color='w', node_shape='o', nodelist=[('/')], ax=a)

            nx.draw_networkx_edges(B, pos, edge_color='g', edgelist=[('ID4', 3)], width=1, arrowsize=14, ax=a)
            nx.draw_networkx_edges(B, pos, edge_color='g', edgelist=[('NUM4', 3)], width=1, arrowsize=14, ax=a)
            nx.draw_networkx_edges(B, pos, edge_color='g', edgelist=[(' ', 2)], width=1, arrowsize=14, ax=a)

            nx.draw_networkx_nodes(B, pos, node_size=300, node_color='LightGreen', node_shape='o', nodelist=[(3)],
                                   edgecolors='black', ax=a)
            nx.draw_networkx_edge_labels(B, pos, edge_labels=nx.get_edge_attributes(B, 'transition'), label_pos=0.7,
                                         font_size=8, ax=a)
            nx.draw_networkx_edges(B, pos, edge_color='r', connectionstyle='arc3, rad = 0.3', edgelist=[(2, 'X')],
                                   width=1,
                                   arrowsize=9, ax=a)
            nx.draw_networkx_edges(B, pos, edge_color='r', connectionstyle='arc3, rad = -0.2', edgelist=[('OP3', 'X')],
                                   width=1, arrowsize=9, ax=a)
            nx.draw_networkx_edges(B, pos, edge_color='r', connectionstyle='arc3, rad = -0.3', edgelist=[('OP4', 'X')],
                                   width=1, arrowsize=9, ax=a)
            # nx.draw_networkx_edges(B,pos,edge_color='r',connectionstyle='arc3, rad = -0.5', edgelist = [(3,'X')] , width=1,arrowsize=9)
            nx.draw_networkx_edges(B, pos, edge_color='b', connectionstyle='arc3, rad = 0.3',
                                   edgelist=[('NUM4', 'OP3')],
                                   width=1, arrowsize=9, ax=a)
            nx.draw_networkx_edges(B, pos, edge_color='b', connectionstyle='arc3, rad = -0.3',
                                   edgelist=[('NUM4', 'OP4')],
                                   width=1, arrowsize=9, ax=a)
            nx.draw_networkx_edges(B, pos, edge_color='b', connectionstyle='arc3, rad = 0.3', edgelist=[('ID4', 'OP3')],
                                   width=1, arrowsize=9, ax=a)
            nx.draw_networkx_edges(B, pos, edge_color='b', connectionstyle='arc3, rad = -0.3',
                                   edgelist=[('ID4', 'OP4')],
                                   width=1, arrowsize=9, ax=a)

            canvas = FigureCanvasTkAgg(f, self)
            # canvas.show()
            canvas.draw()
            canvas.get_tk_widget().pack(side=tk.BOTTOM, fill=tk.BOTH, expand=True)

            toolbar = NavigationToolbar2TkAgg(canvas, self)
            toolbar.update()
            canvas._tkcanvas.pack(side=tk.TOP, fill=tk.BOTH, expand=True)

    root = SeaofBTCapp()
    root.mainloop()


# /////////
CalculateButton = Button(root, text='Calculate', padx=20, pady=20, command=onClick, fg="Yellow", bg="BLUE")
CalculateButton.pack()
showDFAButton = Button(root, text="Show DFA", command=open_win)
# ShowDfaButton = Button(root, text = 'Show DFA')
# ShowDfaButton = Button(root, text = 'Show DFA',command=lambda :s1.show_frame(StartPage))
# ShowDfaButton = Button(root, text = 'Show DFA',command=present)

root.mainloop()

