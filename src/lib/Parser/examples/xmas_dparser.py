#!/usr/bin/python

from parser import *
from path import *

GRAMMAR = 'xmas'

def read_text(filename):
    with open(filename, 'r') as f:
        return f.read()

def read_grammar(revision):
    return read_text('{}.g'.format(revision))

class parse_node(object):
  def __init__(self, node):
    self.node = node

  def __pnode_to_string(self, pnode, print_symbol=True):
    if isinstance(pnode, dparser.D_ParseNode):
      children = [self.__pnode_to_string(c, print_symbol) for c in pnode.c]
      children = [x for x in children if x]
      if children:
        if print_symbol:
          return '{0}({1})'.format(pnode.symbol, ', '.join(children))
        else:
          if len(children) > 1:
            return '({0})'.format(' '.join(children))
          else:
            return children[0]
      else:
        captured = pnode.start_loc.buf[pnode.start_loc.s:pnode.end]
        if print_symbol:
          return '{0}({1})'.format(pnode.symbol, repr(captured))
        return repr(captured) if '(' in captured or ')' in captured else captured
    else:
      if print_symbol:
        return ', '.join(self.__pnode_to_string(c, print_symbol) for c in pnode)
      else:
        return ' '.join(self.__pnode_to_string(c, print_symbol) for c in pnode)

  def text(self):
      return self.node.start_loc.buf[self.node.start_loc.s:self.node.end]

  def children(self):
      return map(parse_node, self.node.c)

  def symbol(self):
      return self.node.symbol

  def __str__(self):
    return self.__pnode_to_string(self.node)

def parse_node_text(node):
    return repr(node.start_loc.buf[node.start_loc.s:node.end])

def parse_node_structure(node):
    return str(parse_node(node))

def print_alternatives(alternatives, msg):
    print '---', msg, 'ambiguity'
    for alt in alternatives:
        print 'ALT', str(parse_node(alt))

def ambiguity_function(alternatives):
    print '--- AMBIGUITY DETECTED ---'
    if len(alternatives) > 1:
        print '========='
        for alt in alternatives:
            print 'ALT', str(parse_node(alt))
        print '========='
    return alternatives

def dparse_expression(text, start_symbol, grammar = read_grammar(GRAMMAR)):
    parser = ParsePrinter(grammar)
    print '============================================================================================'
    print 'parsing {}'.format(text)
    # , dont_merge_epsilon_trees=True, dont_compare_stacks=True
    result = parser(text, dont_use_height_for_disambiguation=False, dont_use_greediness_for_disambiguation=False, start_symbol=start_symbol, ambiguity_fn=ambiguity_function)
    print '\n'.join([parser.pnode_to_string(n) for n in result.getStructure()])
    return result

def parse_id(text, grammar = read_grammar(GRAMMAR)):
    return dparse_expression(text, 'ID', grammar)

def parse_component(text, grammar = read_grammar(GRAMMAR)):
    return dparse_expression(text, 'Component', grammar)

def parse_network(text, grammar = read_grammar(GRAMMAR)):
    return dparse_expression(text, 'Network', grammar)

def parse_expressions():
  parse_expression('1')
  parse_expression('Cache(x, y, arrive, Core())')
  parse_expression('f()')
  parse_expression('type in {req}')

def parse_xmas_file(filename):
  print '---', filename
  try:
    text = read_text(filename)
    parse_network(text)
  except Exception as e:
    print e

def main():
  grammar = read_grammar(GRAMMAR)
  dparse_expression('chan i', 'ParameterList', grammar)
  dparse_expression('bus<2> i', 'BusDeclaration', grammar)
  dparse_expression('Fork(buffer_req_out)', 'PrimitiveExpression', grammar)
  dparse_expression('chan q0, q1 := Fork(Source(type))', 'ChannelDeclaration', grammar)
  dparse_expression('chan req_out, rsp_out', 'ChannelDeclaration', grammar)
  dparse_expression('component DualChannel(bus<2> i) => bus<2> o { }', 'Component', grammar)
  dparse_expression('component Delay(chan i) => chan o { }', 'Component', grammar)
  dparse_expression('let o := CtrlJoin(i, wait)', 'LetStatement', grammar)
  dparse_expression('''chan i''', 'ParameterList', grammar)
  dparse_expression('''component Delay(chan i) => chan o { }''', 'Network', grammar)

  dparse_expression('''
component Delay(chan i) => chan o {
	chan wait := Source(type);
	let o := CtrlJoin(i, wait)
}
''', 'Component', grammar)

  dparse_expression('''
component CreditCounter(chan i) => chan o {
	chan q_in;
	let q_in, o := Fork(Source(type));
	Sink(CtrlJoin(Queue(counters, q_in), i))
}
''', 'Component', grammar)

  dparse_expression('''
component DualChannel(bus<2> i) => bus<2> o {
	chan count_rsp, count_req;

	chan data_in := Merge(CtrlJoin(i[0], count_req), CtrlJoin(i[1], count_rsp));
	chan data_out := Queue(dx, data_in);


	chan buffer_req_in, buffer_rsp_in := Switch(type, data_out);

	chan buffer_req_out := Queue(N, buffer_req_in);
	chan buffer_rsp_out := Queue(N, buffer_rsp_in);

	chan req_out, rsp_out;
	let o[0], req_out := Fork(buffer_req_out);
	let o[1], rsp_out := Fork(buffer_rsp_out);

	let count_rsp := Queue(N, Queue(dx, CreditCounter(rsp_out)));
	let count_req := Queue(N, Queue(dx, CreditCounter(req_out)))
}
''', 'Component', grammar)

  dparse_expression('''
component Agent(bus<2> i) => bus<2> o {
	let o[0] := Source(type);
	Sink(i[1]);

	let o[1] := Function(type, Delay(i[0]))
}
''', 'Component', grammar)

  dparse_expression('''
bus<2> agent0_in;
bus<2> agent0_out := Agent(agent0_in);
bus<2> agent1_out := Agent(DualChannel(agent0_out));
let agent0_in := DualChannel(agent1_out)
''', 'Network', grammar)

  dparse_expression('''
param int dx = 2;
param int N = 2;
param int counters = 2;

component Delay(chan i) => chan o {
	chan wait := Source(type);
	let o := CtrlJoin(i, wait)
}
''', 'Network', grammar)

  parse_xmas_file('bluered.xmas')
  parse_xmas_file('twoagents2_2.xmas')
  parse_xmas_file('reqrsp.xmas')

if __name__ == '__main__':
  main()
