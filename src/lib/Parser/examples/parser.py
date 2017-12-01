#!/usr/bin/python

# author: Sjoerd Cranen

import dparser

class ParsePrinter(object):

  def __init__(self, grammar, **parser_kwargs):
    def d_reduce(t, nodes):
      return nodes
    d_reduce.__doc__ = grammar
    self.parser = dparser.Parser(modules={'d_reduce': d_reduce}, **parser_kwargs)
    self.__err = False

  def __call__(self, text, **parse_kwargs):
    parse_kwargs.setdefault('syntax_error_fn', self.__contexterr(repr(text)))
    parse_kwargs.setdefault('ambiguity_fn', self.__contextamb(repr(text)))
    result = self.parser.parse(text, **parse_kwargs)
    if not self.__err:
      print 'good:', text
      print '     ', self.__pnode_to_string(result.getStructure(), False)
    self.__err = False
    return result

  def __contextamb(self, context):
    def amb(x):
      options = set([self.__pnode_to_string(n, False) for n in x])
      if len(options) == 1:
        options = [self.__pnode_to_string(n, True) for n in x]
      print 'ambiguity in', context
      print '  {0}'.format('\n  '.join(options))
      self.__err = True
    return amb

  def __contexterr(self, context):
    def err(loc):
      before = loc.buf[max(loc.s - 25, 0):loc.s]
      after = loc.buf[loc.s:min(loc.s + 25, len(loc.buf))]
      print 'syntax error on line', loc.line, 'in', context
      print '{0}{1}'.format(before, after)
      print '{0}^'.format(len(before) * '~')
      self.__err = True
    return err

  def __nested_container_to_string(self, t):
    if isinstance(t, (list, tuple)):
      return ' '.join([self.__nested_list_to_string(x) for x in t])
    return t

  def __filter_empty(self, t):
    if isinstance(t, (list, tuple)):
      return any([self.__filter_empty(x) for x in t])
    return t

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
  pnode_to_string = __pnode_to_string

def main():
  parser = ParsePrinter("SortExpr: 'Bool'                                      "
                        "        | SortExpr ('->' $binary_op_right 1) SortExpr "
                        "        | SortExpr ('#' $binary_op_left 2) SortExpr   "
                        "        | '(' SortExpr ')'")

  def parse(string):
    return parser(string, dont_use_greediness_for_disambiguation=True)

  parse('Bool')
  parse('Bool -> Bool')
  parse('Bool # Bool -> Bool')
  parse('Bool # Bool # Bool -> Bool')
  parse('Bool # Bool # Bool')
  parse('Bool # Bool # Bool -> Bool -> Bool')
  parse('Bool -> Bool # Bool -> Bool')

  parse('(Bool -> Bool)')
  parse('Bool -> (Bool -> Bool)')
  parse('Bool # (Bool -> Bool) -> Bool')
  parse('Bool # (Bool -> Bool) # Bool -> Bool')
  parse('Bool # (Bool) # Bool -> Bool -> Bool')
  parse('Bool # (Bool -> Bool) # Bool -> Bool -> Bool')
  parse('((Bool -> Bool) # Bool # Bool) -> (Bool-> Bool)')

if __name__ == '__main__':
  main()

