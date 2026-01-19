import re


def flatten_tuple(x):
    if not isinstance(x, tuple):
        return x,
    result = ()
    for y in x:
        result += flatten_tuple(y)
    return result


class Parser:
    def match(self, s):
        raise NotImplementedError()

    def then(self, parser):
        return Then(self, parser)

    def then1(self, parser):
        return Apply(Then(self, parser), lambda p: p[0])

    def then2(self, parser):
        return Apply(Then(self, parser), lambda p: p[1])

    def alt(self, parser):
        return Alt(self, parser)

    def apply(self, function):
        return Apply(self, function)

    def lift(self, parser):
        return Lift(self, parser)

    def flatten(self):
        return Apply(self, flatten_tuple)


class String(Parser):
    def __init__(self, string):
        self.string = string

    def match(self, s):
        if s.startswith(self.string):
            return self.string, s[len(self.string):]
        return None


class Regex(Parser):
    def __init__(self, re_string):
        self.re = re.compile(re_string)

    def match(self, s):
        match = self.re.match(s)
        if match is None:
            return None
        l, r = match.span()
        if l > 0:
            return None
        return s[:r], s[r:].lstrip()


class Optional(Parser):
    def __init__(self, parser):
        self.parser = parser

    def match(self, s):
        match = self.parser.match(s)
        if match is None:
            return None, s
        return match


class Then(Parser):
    def __init__(self, first, second):
        self.first = first
        self.second = second

    def match(self, s):
        match = self.first.match(s)
        if match is None:
            return None
        x, s = match
        s = s.lstrip()
        match = self.second.match(s)
        if match is None:
            return None
        y, s = match
        return (x, y), s


class Apply(Parser):
    def __init__(self, parser, function):
        self.parser = parser
        self.function = function

    def match(self, s):
        match = self.parser.match(s)
        if match is None:
            return None
        x, s = match
        return self.function(x), s


class Alt(Parser):
    def __init__(self, first, second):
        self.first = first
        self.second = second

    def match(self, s):
        match = self.first.match(s)
        if match is None:
            return self.second.match(s)
        return match


class Lift(Parser):
    def __init__(self, first, second):
        self.first = first
        self.second = second

    def match(self, s):
        match = self.first.match(s)
        if match is None:
            return None
        x, s = match
        match = self.second.match(x)
        if match is None:
            return None
        y, s1 = match
        if s1.strip() == "":
            return y, s
        return None


class Parens(Parser):
    def __init__(self, left, right):
        self.left = left
        self.right = right

    def match(self, s):
        count = 0
        if len(s) == 0 or s[0] != self.left:
            return None
        for i in range(len(s)):
            c = s[i]
            if c == self.left:
                count += 1
            elif c == self.right:
                count -= 1
                if count < 0:
                    count = 0
                elif count == 0:
                    return s[1:i], s[i+1:]
        return None


class ListParser(Parser):
    def __init__(self, separator, parser):
        self.separator = separator
        self.parser = parser

    def match(self, s):
        start = self.parser.match(s)
        if start is None:
            return None
        start, s = start
        parts = [start]
        while len(s) > 0:
            s = s.lstrip()
            if s.startswith(self.separator):
                s2 = s.lstrip(self.separator)
                s2 = s2.lstrip()
                result = self.parser.match(s2)
                if result is None:
                    return parts, s
                x, s = result
                parts.append(x)
            else:
                break
        return parts, s


if __name__ == "__main__":
    print("=" * 100)
    print("Running test cases for parser combinators!")
    print("=" * 100)

    test = "P1_x=P2_x & 6<P1_x & 4<P2_x & 2<P3_x & 6<P4_x & 2<P1_x-P2_x & 4<P1_x-P3_x & 0<=P1_x-P4_x & 2<P2_x-P3_x & P2_x-P4_x<-2 & P3_x-P4_x<-4"
    p = ListParser('&', Regex("[\w=\<\-]+"))
    print(p.match(test))

    re_identifier = re.compile("\w+")
    ident_parser = Regex(re_identifier)
    test = "1,2,3,4"
    p = ListParser(',', ident_parser)
    print(p.match(test))
