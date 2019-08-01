"""Generated low-level arithmetic methods for CollectingField.

This file is generated by the src/mk_pairs_ops.py script.
See http://sympycore.googlecode.com/ for more information.

DO NOT CHANGE THIS FILE DIRECTLY!!!
"""

from ..core import Expr
from ..utils import NUMBER, SYMBOL, TERMS
from ..heads import BASE_EXP_DICT as FACTORS
from ..arithmetic.numbers import (normalized_fraction, mpq, try_power,
  numbertypes, inttypes_set, numbertypes_set)
from ..arithmetic.infinity import Infinity

def div(a, b, cls):
    if type(b) in inttypes_set:
        if type(a) in inttypes_set:
            if not b:
                if not a:
                    return cls.undefined
                return cls.zoo
            return normalized_fraction(a, b)
        if not b:
            return a * cls.zoo
        if b == 1:
            return a
        return a * mpq((1,b))
    return a / b




def expand_mul_method(cls, self, other):
    lhead, ldata = self.pair
    rhead, rdata = other.pair
    if lhead is FACTORS:
        if rhead is FACTORS:
            #MUL_FACTORS_FACTORS(LHS=self; LHSDATA=ldata; RHS=other; RHSDATA=rdata)
            pairs = ldata.copy()
            pairs_get = pairs.get
            number = 1
            for t,c in rdata.iteritems():
                #MUL_FACTOR_VALUE_DICT(FACTOR=t; SIGN=+; USIGN=; VALUE=c; DICT=pairs; DICT_GET=pairs_get; NUMBER=number)
                _tmp9 = pairs_get(t)
                if _tmp9 is None:
                    pairs[t] =  c
                else:
                    _tmp9 = _tmp9 + c
                    if type(_tmp9) is cls and _tmp9.head is NUMBER:
                        _tmp9 = _tmp9.data
                    if _tmp9:
                        if t.head is NUMBER:
                            del pairs[t]
                            z, sym = try_power(t.data, _tmp9)
                            if sym:
                                for t1, c1 in sym:
                                    #NEWINSTANCE(OBJ=tt; HEAD=NUMBER; DATA=t1)
                                    tt = cls(NUMBER, t1)
                                    #ADD_TERM_VALUE_DICT(DICT=pairs; DICT_GET=pairs_get; TERM=tt; VALUE=c1; SIGN=+; USIGN=)
                                    _tmp23 = pairs_get(tt)
                                    if _tmp23 is None:
                                        pairs[tt] =  c1
                                    else:
                                        _tmp23 = _tmp23 + c1
                                        if _tmp23:
                                            pairs[tt] = _tmp23
                                        else:
                                            del pairs[tt]
                            number = number * z
                        else:
                            pairs[t] = _tmp9
                    else:
                        del pairs[t]
            #CANONIZE_FACTORS_DICT(DICT=pairs; NUMBER=number)
            if not pairs:
                if number is 1:
                    return cls.one
                return number
            if len(pairs)==1:
               t, c = pairs.items()[0]
               if c==1:
                   if number==1:
                       return t
                   #RETURN_NEW(HEAD=TERMS; DATA={t: number})
                   #NEWINSTANCE(OBJ=_tmp37; HEAD=TERMS; DATA={t: number})
                   _tmp37 = cls(TERMS, {t: number})
                   return _tmp37
               if t==cls.one:
                   return number
            if number == 1:
                #RETURN_NEW(HEAD=FACTORS; DATA=pairs)
                #NEWINSTANCE(OBJ=_tmp51; HEAD=FACTORS; DATA=pairs)
                _tmp51 = cls(FACTORS, pairs)
                return _tmp51
            #NEWINSTANCE(OBJ=obj; HEAD=FACTORS; DATA=pairs)
            obj = cls(FACTORS, pairs)
            #RETURN_NEW(HEAD=TERMS; DATA={obj: number})
            #NEWINSTANCE(OBJ=_tmp72; HEAD=TERMS; DATA={obj: number})
            _tmp72 = cls(TERMS, {obj: number})
            return _tmp72
        elif rhead is NUMBER:
            return self # other must be one
        else:
            #MUL_FACTORS_SYMBOL(LHS=self; LHSDATA=ldata; RHS=other; RHSDATA=rdata)
            pairs = ldata.copy()
            #MUL_DICT_SYMBOL(DICT=pairs; RHS=other; RHSDATA=rdata)
            #ADD_TERM_VALUE_DICT(TERM=other; VALUE=1; DICT=pairs; DICT_GET=pairs.get; SIGN=+; USIGN=)
            _tmp100 = pairs.get(other)
            if _tmp100 is None:
                pairs[other] =  1
            else:
                _tmp100 = _tmp100 + 1
                if _tmp100:
                    pairs[other] = _tmp100
                else:
                    del pairs[other]
            #CANONIZE_FACTORS_DICT1(DICT=pairs)
            if not pairs:
                return cls.one
            if len(pairs)==1:
               t, c = pairs.items()[0]
               if c==1:
                   return t
               if t==cls.one:
                   return t
            #RETURN_NEW(HEAD=FACTORS; DATA=pairs)
            #NEWINSTANCE(OBJ=_tmp114; HEAD=FACTORS; DATA=pairs)
            _tmp114 = cls(FACTORS, pairs)
            return _tmp114
    elif lhead is NUMBER:
        return other # self must be one
    else:
        if rhead is FACTORS:
            #MUL_SYMBOL_FACTORS(LHS=self; LHSDATA=ldata; RHS=other; RHSDATA=rdata)
            #MUL_FACTORS_SYMBOL(LHS=other; LHSDATA=rdata; RHS=self; RHSDATA=ldata)
            pairs = rdata.copy()
            #MUL_DICT_SYMBOL(DICT=pairs; RHS=self; RHSDATA=ldata)
            #ADD_TERM_VALUE_DICT(TERM=self; VALUE=1; DICT=pairs; DICT_GET=pairs.get; SIGN=+; USIGN=)
            _tmp149 = pairs.get(self)
            if _tmp149 is None:
                pairs[self] =  1
            else:
                _tmp149 = _tmp149 + 1
                if _tmp149:
                    pairs[self] = _tmp149
                else:
                    del pairs[self]
            #CANONIZE_FACTORS_DICT1(DICT=pairs)
            if not pairs:
                return cls.one
            if len(pairs)==1:
               t, c = pairs.items()[0]
               if c==1:
                   return t
               if t==cls.one:
                   return t
            #RETURN_NEW(HEAD=FACTORS; DATA=pairs)
            #NEWINSTANCE(OBJ=_tmp163; HEAD=FACTORS; DATA=pairs)
            _tmp163 = cls(FACTORS, pairs)
            return _tmp163
        elif rhead is NUMBER:
            return self # other must be one
        else:
            #MUL_SYMBOL_SYMBOL(LHS=self; LHSDATA=ldata; RHS=other; RHSDATA=rdata)
            if self == other:
                pairs = {self: 2}
            else:
                pairs = {self: 1, other: 1}
            #RETURN_NEW(HEAD=FACTORS; DATA=pairs)
            #NEWINSTANCE(OBJ=_tmp184; HEAD=FACTORS; DATA=pairs)
            _tmp184 = cls(FACTORS, pairs)
            return _tmp184

#def rsub_method(self, other, NUMBER=NUMBER, TERMS=TERMS, FACTORS=FACTORS):
#    cls = type(self)
#    lhead, ldata = self.pair
#    if isinstance(other, cls.coefftypes):
#        if lhead is NUMBER:
#            @SUB_VALUE_NUMBER(VALUE=other; RHS=self; RHSDATA=ldata)
#        elif lhead is TERMS:
#            @SUB_VALUE_TERMS(VALUE=other; RHS=self; RHSDATA=ldata)
#        else:
#            @SUB_VALUE_SYMBOL(VALUE=other; RHS=self; RHSDATA=ldata)
#    other = cls.convert(other, False)
#    if other is NotImplemented:
#        return other
#    return other - self

def rdiv_method(self, other, NUMBER=NUMBER, TERMS=TERMS, FACTORS=FACTORS):
    cls = type(self)
    lhead, ldata = self.pair
    if isinstance(other, cls.coefftypes):
        if lhead is NUMBER:
            #DIV_VALUE_NUMBER(VALUE=other; RHS=self; RHSDATA=ldata)
            #RETURN_NEW2(HEAD=NUMBER; DATA=div(other, ldata, cls))
            _tmp205 = div(other, ldata, cls)
            if isinstance(_tmp205, Infinity):
                return _tmp205
            #RETURN_NEW(HEAD=NUMBER; DATA=_tmp205)
            #NEWINSTANCE(OBJ=_tmp212; HEAD=NUMBER; DATA=_tmp205)
            _tmp212 = cls(NUMBER, _tmp205)
            return _tmp212
        elif lhead is TERMS:
            #DIV_VALUE_TERMS(VALUE=other; RHS=self; RHSDATA=ldata)
            _tmp226 = other
            if not _tmp226:
                return cls.zero
            pairs = ldata
            if len(pairs)==1:
                t, c = pairs.items()[0]
                c = div(other, c, cls)
                t = 1/t
                if c==1:
                    return t
                if t==cls.one:
                    return cls(NUMBER, c)
                #RETURN_NEW(HEAD=TERMS; DATA={t: c})
                #NEWINSTANCE(OBJ=_tmp233; HEAD=TERMS; DATA={t: c})
                _tmp233 = cls(TERMS, {t: c})
                return _tmp233
            #NEWINSTANCE(OBJ=_tmp226; HEAD=FACTORS; DATA={self: -1})
            _tmp226 = cls(FACTORS, {self: -1})
            if other==1:
                return _tmp226
            #RETURN_NEW(HEAD=TERMS; DATA={_tmp226: other})
            #NEWINSTANCE(OBJ=_tmp254; HEAD=TERMS; DATA={_tmp226: other})
            _tmp254 = cls(TERMS, {_tmp226: other})
            return _tmp254
        elif lhead is FACTORS:
            #DIV_VALUE_FACTORS(VALUE=other; RHS=self; RHSDATA=ldata)
            
            pairs = ldata
            if len(pairs)==1:
                t, c = pairs.items()[0]
                c = -c
                if c==1:
                    return t * other
                new_pairs = {t: c}
            else:
                #NEG_DICT_VALUES(DICT_IN=pairs; DICT_OUT=new_pairs)
                new_pairs = dict([(t, -c) for t,c in pairs.iteritems()])
            #NEWINSTANCE(OBJ=_tmp268; HEAD=FACTORS; DATA=new_pairs)
            _tmp268 = cls(FACTORS, new_pairs)
            if other==1:
                return _tmp268
            #RETURN_NEW(HEAD=TERMS; DATA={_tmp268: other})
            #NEWINSTANCE(OBJ=_tmp289; HEAD=TERMS; DATA={_tmp268: other})
            _tmp289 = cls(TERMS, {_tmp268: other})
            return _tmp289
        else:
            #DIV_VALUE_SYMBOL(VALUE=other; RHS=self; RHSDATA=ldata)
            _tmp303 = other
            if not _tmp303:
                return cls.zero
            #NEWINSTANCE(OBJ=obj2; HEAD=FACTORS; DATA={self: -1})
            obj2 = cls(FACTORS, {self: -1})
            if _tmp303==1:
                return obj2
            #RETURN_NEW(HEAD=TERMS; DATA={obj2: _tmp303})
            #NEWINSTANCE(OBJ=_tmp317; HEAD=TERMS; DATA={obj2: _tmp303})
            _tmp317 = cls(TERMS, {obj2: _tmp303})
            return _tmp317
    other = cls.convert(other, False)
    if other is NotImplemented:
        return other
    return other / self


def div_method(self, other, NUMBER=NUMBER, TERMS=TERMS, FACTORS=FACTORS):
    cls = type(self)
    lhead, ldata = self.pair
    if type(other) is not cls:
        if isinstance(other, cls.coefftypes):
            if lhead is NUMBER:
                #DIV_NUMBER_VALUE(VALUE=other; LHS=self; LHSDATA=ldata)
                #RETURN_NEW2(HEAD=NUMBER; DATA=div(ldata, other, cls))
                _tmp338 = div(ldata, other, cls)
                if isinstance(_tmp338, Infinity):
                    return _tmp338
                #RETURN_NEW(HEAD=NUMBER; DATA=_tmp338)
                #NEWINSTANCE(OBJ=_tmp345; HEAD=NUMBER; DATA=_tmp338)
                _tmp345 = cls(NUMBER, _tmp338)
                return _tmp345
            elif lhead is TERMS:
                #DIV_TERMS_VALUE(VALUE=other; LHS=self; LHSDATA=ldata)
                #MUL_TERMS_VALUE(LHS=self; LHSDATA=ldata; VALUE=div(1,other,cls))
                #MUL_VALUE_TERMS(VALUE=div(1,other,cls); RHS=self; RHSDATA=ldata)
                _tmp373 = div(1,other,cls)
                if not _tmp373:
                    return cls.zero
                pairs = ldata
                if len(pairs)==1:
                    t, c = pairs.items()[0]
                    c = _tmp373 * c
                    if c==1:
                        return t
                    #RETURN_NEW(HEAD=TERMS; DATA={t: c})
                    #NEWINSTANCE(OBJ=_tmp380; HEAD=TERMS; DATA={t: c})
                    _tmp380 = cls(TERMS, {t: c})
                    return _tmp380
                if _tmp373==1:
                    return self
                pairs = {}
                for t,c in ldata.iteritems():
                    pairs[t] = _tmp373 * c
                #NEWINSTANCE(OBJ=obj; HEAD=TERMS; DATA=pairs)
                obj = cls(TERMS, pairs)
                coeff, terms = self._coeff_terms
                if terms is not None:
                    c = coeff * _tmp373
                    if not c==1:
                        obj._coeff_terms = (c, terms)
                else:
                    obj._coeff_terms = (_tmp373, self)
                return obj
            elif lhead is FACTORS:
                #DIV_FACTORS_VALUE(VALUE=other; LHS=self; LHSDATA=ldata)
                #MUL_FACTORS_VALUE(LHS=self; LHSDATA=ldata; VALUE=div(1,other,cls))
                #MUL_SYMBOL_VALUE(VALUE=div(1,other,cls); LHS=self; LHSDATA=ldata)
                #MUL_VALUE_SYMBOL(VALUE=div(1,other,cls); RHS=self; RHSDATA=ldata)
                _tmp422 = div(1,other,cls)
                if not _tmp422:
                    return cls.zero
                if _tmp422==1:
                    return self
                #RETURN_NEW(HEAD=TERMS; DATA={self: _tmp422})
                #NEWINSTANCE(OBJ=_tmp429; HEAD=TERMS; DATA={self: _tmp422})
                _tmp429 = cls(TERMS, {self: _tmp422})
                return _tmp429
            else:
                #DIV_SYMBOL_VALUE(VALUE=other; LHS=self; LHSDATA=ldata)
                #MUL_VALUE_SYMBOL(VALUE=div(1, other, cls); RHS=self; RHSDATA=ldata)
                _tmp450 = div(1, other, cls)
                if not _tmp450:
                    return cls.zero
                if _tmp450==1:
                    return self
                #RETURN_NEW(HEAD=TERMS; DATA={self: _tmp450})
                #NEWINSTANCE(OBJ=_tmp457; HEAD=TERMS; DATA={self: _tmp450})
                _tmp457 = cls(TERMS, {self: _tmp450})
                return _tmp457
        other = cls.convert(other, False)
        if other is NotImplemented:
            return other
    rhead, rdata = other.pair
    if lhead is NUMBER:
        if rhead is NUMBER:
            #DIV_NUMBER_NUMBER(LHS=self; LHSDATA=ldata; RHS=other; RHSDATA=rdata)
            #DIV_VALUE_NUMBER(VALUE=ldata; RHS=other; RHSDATA=rdata)
            #RETURN_NEW2(HEAD=NUMBER; DATA=div(ldata, rdata, cls))
            _tmp485 = div(ldata, rdata, cls)
            if isinstance(_tmp485, Infinity):
                return _tmp485
            #RETURN_NEW(HEAD=NUMBER; DATA=_tmp485)
            #NEWINSTANCE(OBJ=_tmp492; HEAD=NUMBER; DATA=_tmp485)
            _tmp492 = cls(NUMBER, _tmp485)
            return _tmp492
        elif rhead is TERMS:
            #DIV_NUMBER_TERMS(LHS=self; LHSDATA=ldata; RHS=other; RHSDATA=rdata)
            #DIV_VALUE_TERMS(VALUE=ldata; RHS=other; RHSDATA=rdata)
            _tmp513 = ldata
            if not _tmp513:
                return cls.zero
            pairs = rdata
            if len(pairs)==1:
                t, c = pairs.items()[0]
                c = div(ldata, c, cls)
                t = 1/t
                if c==1:
                    return t
                if t==cls.one:
                    return cls(NUMBER, c)
                #RETURN_NEW(HEAD=TERMS; DATA={t: c})
                #NEWINSTANCE(OBJ=_tmp520; HEAD=TERMS; DATA={t: c})
                _tmp520 = cls(TERMS, {t: c})
                return _tmp520
            #NEWINSTANCE(OBJ=_tmp513; HEAD=FACTORS; DATA={other: -1})
            _tmp513 = cls(FACTORS, {other: -1})
            if ldata==1:
                return _tmp513
            #RETURN_NEW(HEAD=TERMS; DATA={_tmp513: ldata})
            #NEWINSTANCE(OBJ=_tmp541; HEAD=TERMS; DATA={_tmp513: ldata})
            _tmp541 = cls(TERMS, {_tmp513: ldata})
            return _tmp541
        elif rhead is FACTORS:
            #DIV_NUMBER_FACTORS(LHS=self; LHSDATA=ldata; RHS=other; RHSDATA=rdata)
            #DIV_VALUE_FACTORS(VALUE=ldata; RHS=other; RHSDATA=rdata)
            
            pairs = rdata
            if len(pairs)==1:
                t, c = pairs.items()[0]
                c = -c
                if c==1:
                    return t * ldata
                new_pairs = {t: c}
            else:
                #NEG_DICT_VALUES(DICT_IN=pairs; DICT_OUT=new_pairs)
                new_pairs = dict([(t, -c) for t,c in pairs.iteritems()])
            #NEWINSTANCE(OBJ=_tmp562; HEAD=FACTORS; DATA=new_pairs)
            _tmp562 = cls(FACTORS, new_pairs)
            if ldata==1:
                return _tmp562
            #RETURN_NEW(HEAD=TERMS; DATA={_tmp562: ldata})
            #NEWINSTANCE(OBJ=_tmp583; HEAD=TERMS; DATA={_tmp562: ldata})
            _tmp583 = cls(TERMS, {_tmp562: ldata})
            return _tmp583
        else:
            #DIV_NUMBER_SYMBOL(LHS=self; LHSDATA=ldata; RHS=other; RHSDATA=rdata)
            #DIV_VALUE_SYMBOL(VALUE=ldata; RHS=other; RHSDATA=rdata)
            _tmp604 = ldata
            if not _tmp604:
                return cls.zero
            #NEWINSTANCE(OBJ=obj2; HEAD=FACTORS; DATA={other: -1})
            obj2 = cls(FACTORS, {other: -1})
            if _tmp604==1:
                return obj2
            #RETURN_NEW(HEAD=TERMS; DATA={obj2: _tmp604})
            #NEWINSTANCE(OBJ=_tmp618; HEAD=TERMS; DATA={obj2: _tmp604})
            _tmp618 = cls(TERMS, {obj2: _tmp604})
            return _tmp618
    elif lhead is TERMS:
        if rhead is NUMBER:
            #DIV_TERMS_NUMBER(LHS=self; LHSDATA=ldata; RHS=other; RHSDATA=rdata)
            #DIV_TERMS_VALUE(VALUE=rdata; LHS=self; LHSDATA=ldata)
            #MUL_TERMS_VALUE(LHS=self; LHSDATA=ldata; VALUE=div(1,rdata,cls))
            #MUL_VALUE_TERMS(VALUE=div(1,rdata,cls); RHS=self; RHSDATA=ldata)
            _tmp653 = div(1,rdata,cls)
            if not _tmp653:
                return cls.zero
            pairs = ldata
            if len(pairs)==1:
                t, c = pairs.items()[0]
                c = _tmp653 * c
                if c==1:
                    return t
                #RETURN_NEW(HEAD=TERMS; DATA={t: c})
                #NEWINSTANCE(OBJ=_tmp660; HEAD=TERMS; DATA={t: c})
                _tmp660 = cls(TERMS, {t: c})
                return _tmp660
            if _tmp653==1:
                return self
            pairs = {}
            for t,c in ldata.iteritems():
                pairs[t] = _tmp653 * c
            #NEWINSTANCE(OBJ=obj; HEAD=TERMS; DATA=pairs)
            obj = cls(TERMS, pairs)
            coeff, terms = self._coeff_terms
            if terms is not None:
                c = coeff * _tmp653
                if not c==1:
                    obj._coeff_terms = (c, terms)
            else:
                obj._coeff_terms = (_tmp653, self)
            return obj
        elif rhead is TERMS:
            #DIV_TERMS_TERMS(LHS=self; LHSDATA=ldata; RHS=other; RHSDATA=rdata)
            
            if self==other:
                return cls.one
            lpairs = ldata
            rpairs = rdata
            if len(lpairs)==1:
                t1, c1 = lpairs.items()[0]
                if len(rpairs)==1:
                    t2, c2 = rpairs.items()[0]
                    c = div(c1, c2, cls)
                    if t2==t1:
                        return cls(NUMBER, c)
                    if c==1:
                        return t1 / t2
                        #@RETURN_NEW(HEAD=FACTORS; DATA={t1:1, t2:-1})
                    return (t1 / t2) * c
                    #@NEWINSTANCE(OBJ=_tmp681; HEAD=FACTORS; DATA={t1:1, t2:-1})
                else:
                    _tmp681 = t1 / other
                #RETURN_NEW(HEAD=TERMS; DATA={_tmp681:c1})
                #NEWINSTANCE(OBJ=_tmp688; HEAD=TERMS; DATA={_tmp681:c1})
                _tmp688 = cls(TERMS, {_tmp681:c1})
                return _tmp688
            elif len(rpairs)==1:
                t2, c2 = rpairs.items()[0]
                c = div(1, c2, cls)
                if t2==self:
                    return cls(NUMBER, c)
                _tmp681 = self / t2
                #RETURN_NEW(HEAD=TERMS; DATA={_tmp681:c})
                #NEWINSTANCE(OBJ=_tmp702; HEAD=TERMS; DATA={_tmp681:c})
                _tmp702 = cls(TERMS, {_tmp681:c})
                return _tmp702
            #RETURN_NEW(HEAD=FACTORS; DATA={self:1, other:-1})
            #NEWINSTANCE(OBJ=_tmp716; HEAD=FACTORS; DATA={self:1, other:-1})
            _tmp716 = cls(FACTORS, {self:1, other:-1})
            return _tmp716
        elif rhead is FACTORS:
            #DIV_TERMS_FACTORS(LHS=self; LHSDATA=ldata; RHS=other; RHSDATA=rdata)
            lpairs = ldata
            if len(lpairs)==1:
                t, c = lpairs.items()[0]
                t = t / other
                if t==cls.one:
                    return cls(NUMBER, c)
                head, data = t.pair
                if head is NUMBER:
                    #RETURN_NEW(HEAD=NUMBER; DATA=data * c)
                    #NEWINSTANCE(OBJ=_tmp737; HEAD=NUMBER; DATA=data * c)
                    _tmp737 = cls(NUMBER, data * c)
                    return _tmp737
                elif head is TERMS:
                    #MUL_TERMS_VALUE(LHS=t; LHSDATA=data; VALUE=c)
                    #MUL_VALUE_TERMS(VALUE=c; RHS=t; RHSDATA=data)
                    _tmp758 = c
                    if not _tmp758:
                        return cls.zero
                    pairs = data
                    if len(pairs)==1:
                        t, c = pairs.items()[0]
                        c = _tmp758 * c
                        if c==1:
                            return t
                        #RETURN_NEW(HEAD=TERMS; DATA={t: c})
                        #NEWINSTANCE(OBJ=_tmp765; HEAD=TERMS; DATA={t: c})
                        _tmp765 = cls(TERMS, {t: c})
                        return _tmp765
                    if _tmp758==1:
                        return t
                    pairs = {}
                    for t,c in data.iteritems():
                        pairs[t] = _tmp758 * c
                    #NEWINSTANCE(OBJ=obj; HEAD=TERMS; DATA=pairs)
                    obj = cls(TERMS, pairs)
                    coeff, terms = t._coeff_terms
                    if terms is not None:
                        c = coeff * _tmp758
                        if not c==1:
                            obj._coeff_terms = (c, terms)
                    else:
                        obj._coeff_terms = (_tmp758, t)
                    return obj
                else:
                    #MUL_SYMBOL_VALUE(LHS=t; LHSDATA=data; VALUE=c)
                    #MUL_VALUE_SYMBOL(VALUE=c; RHS=t; RHSDATA=data)
                    _tmp793 = c
                    if not _tmp793:
                        return cls.zero
                    if _tmp793==1:
                        return t
                    #RETURN_NEW(HEAD=TERMS; DATA={t: _tmp793})
                    #NEWINSTANCE(OBJ=_tmp800; HEAD=TERMS; DATA={t: _tmp793})
                    _tmp800 = cls(TERMS, {t: _tmp793})
                    return _tmp800
            #DIV_SYMBOL_FACTORS(LHS=self; LHSDATA=ldata; RHS=other; RHSDATA=rdata)
            pairs = rdata
            if len(pairs)==1:
                t, c = pairs.items()[0]
                if t==self:
                    c = 1 - c
                    if not c:
                        return cls.one
                    if c==1:
                        return t
                    else:
                        #RETURN_NEW(HEAD=FACTORS; DATA={t: c})
                        #NEWINSTANCE(OBJ=_tmp821; HEAD=FACTORS; DATA={t: c})
                        _tmp821 = cls(FACTORS, {t: c})
                        return _tmp821
                #RETURN_NEW(HEAD=FACTORS; DATA={t: -c, self: 1})
                #NEWINSTANCE(OBJ=_tmp835; HEAD=FACTORS; DATA={t: -c, self: 1})
                _tmp835 = cls(FACTORS, {t: -c, self: 1})
                return _tmp835
            #NEG_DICT_VALUES(DICT_IN=rdata; DICT_OUT=pairs)
            pairs = dict([(t, -c) for t,c in rdata.iteritems()])
            #MUL_DICT_SYMBOL(DICT=pairs; RHS=self; RHSDATA=ldata)
            #ADD_TERM_VALUE_DICT(TERM=self; VALUE=1; DICT=pairs; DICT_GET=pairs.get; SIGN=+; USIGN=)
            _tmp863 = pairs.get(self)
            if _tmp863 is None:
                pairs[self] =  1
            else:
                _tmp863 = _tmp863 + 1
                if _tmp863:
                    pairs[self] = _tmp863
                else:
                    del pairs[self]
            #CANONIZE_FACTORS_DICT1(DICT=pairs)
            if not pairs:
                return cls.one
            if len(pairs)==1:
               t, c = pairs.items()[0]
               if c==1:
                   return t
               if t==cls.one:
                   return t
            #RETURN_NEW(HEAD=FACTORS; DATA=pairs)
            #NEWINSTANCE(OBJ=_tmp877; HEAD=FACTORS; DATA=pairs)
            _tmp877 = cls(FACTORS, pairs)
            return _tmp877
        else:
            #DIV_TERMS_SYMBOL(LHS=self; LHSDATA=ldata; RHS=other; RHSDATA=rdata)
            
            pairs = ldata
            if len(pairs)==1:
                t, c = pairs.items()[0]
                if t==other:
                    return cls(NUMBER, c)
                if t.head is FACTORS:
                    _tmp891 = t / other
                    #RETURN_NEW(HEAD=TERMS; DATA={_tmp891: c})
                    #NEWINSTANCE(OBJ=_tmp898; HEAD=TERMS; DATA={_tmp891: c})
                    _tmp898 = cls(TERMS, {_tmp891: c})
                    return _tmp898
                #NEWINSTANCE(OBJ=_tmp891; HEAD=FACTORS; DATA={t:1, other: -1})
                _tmp891 = cls(FACTORS, {t:1, other: -1})
                #RETURN_NEW(HEAD=TERMS; DATA={_tmp891: c})
                #NEWINSTANCE(OBJ=_tmp919; HEAD=TERMS; DATA={_tmp891: c})
                _tmp919 = cls(TERMS, {_tmp891: c})
                return _tmp919
            #RETURN_NEW(HEAD=FACTORS; DATA={self: 1, other: -1})
            #NEWINSTANCE(OBJ=_tmp933; HEAD=FACTORS; DATA={self: 1, other: -1})
            _tmp933 = cls(FACTORS, {self: 1, other: -1})
            return _tmp933
    elif lhead is FACTORS:
        if rhead is NUMBER:
            #DIV_FACTORS_NUMBER(LHS=self; LHSDATA=ldata; RHS=other; RHSDATA=rdata)
            #DIV_FACTORS_VALUE(VALUE=rdata; LHS=self; LHSDATA=ldata)
            #MUL_FACTORS_VALUE(LHS=self; LHSDATA=ldata; VALUE=div(1,rdata,cls))
            #MUL_SYMBOL_VALUE(VALUE=div(1,rdata,cls); LHS=self; LHSDATA=ldata)
            #MUL_VALUE_SYMBOL(VALUE=div(1,rdata,cls); RHS=self; RHSDATA=ldata)
            _tmp975 = div(1,rdata,cls)
            if not _tmp975:
                return cls.zero
            if _tmp975==1:
                return self
            #RETURN_NEW(HEAD=TERMS; DATA={self: _tmp975})
            #NEWINSTANCE(OBJ=_tmp982; HEAD=TERMS; DATA={self: _tmp975})
            _tmp982 = cls(TERMS, {self: _tmp975})
            return _tmp982
        elif rhead is TERMS:
            #DIV_FACTORS_TERMS(LHS=self; LHSDATA=ldata; RHS=other; RHSDATA=rdata)
            rpairs = rdata
            if len(rpairs)==1:
                t, c = rpairs.items()[0]
                t = self / t
                c = div(1, c, cls)
                if t==cls.one:
                    return cls(NUMBER, c)
                head, data = t.pair
                if head is NUMBER:
                    #RETURN_NEW(HEAD=NUMBER; DATA=data * c)
                    #NEWINSTANCE(OBJ=_tmp1003; HEAD=NUMBER; DATA=data * c)
                    _tmp1003 = cls(NUMBER, data * c)
                    return _tmp1003
                elif head is TERMS:
                    #MUL_TERMS_VALUE(LHS=t; LHSDATA=data; VALUE=c)
                    #MUL_VALUE_TERMS(VALUE=c; RHS=t; RHSDATA=data)
                    _tmp1024 = c
                    if not _tmp1024:
                        return cls.zero
                    pairs = data
                    if len(pairs)==1:
                        t, c = pairs.items()[0]
                        c = _tmp1024 * c
                        if c==1:
                            return t
                        #RETURN_NEW(HEAD=TERMS; DATA={t: c})
                        #NEWINSTANCE(OBJ=_tmp1031; HEAD=TERMS; DATA={t: c})
                        _tmp1031 = cls(TERMS, {t: c})
                        return _tmp1031
                    if _tmp1024==1:
                        return t
                    pairs = {}
                    for t,c in data.iteritems():
                        pairs[t] = _tmp1024 * c
                    #NEWINSTANCE(OBJ=obj; HEAD=TERMS; DATA=pairs)
                    obj = cls(TERMS, pairs)
                    coeff, terms = t._coeff_terms
                    if terms is not None:
                        c = coeff * _tmp1024
                        if not c==1:
                            obj._coeff_terms = (c, terms)
                    else:
                        obj._coeff_terms = (_tmp1024, t)
                    return obj
                else:
                    #MUL_SYMBOL_VALUE(LHS=t; LHSDATA=data; VALUE=c)
                    #MUL_VALUE_SYMBOL(VALUE=c; RHS=t; RHSDATA=data)
                    _tmp1059 = c
                    if not _tmp1059:
                        return cls.zero
                    if _tmp1059==1:
                        return t
                    #RETURN_NEW(HEAD=TERMS; DATA={t: _tmp1059})
                    #NEWINSTANCE(OBJ=_tmp1066; HEAD=TERMS; DATA={t: _tmp1059})
                    _tmp1066 = cls(TERMS, {t: _tmp1059})
                    return _tmp1066
            #DIV_FACTORS_SYMBOL(LHS=self; LHSDATA=ldata; RHS=other; RHSDATA=rdata)
            pairs = ldata.copy()
            #DIV_DICT_SYMBOL(RHS=other; RHSDATA=rdata; DICT=pairs)
            #ADD_TERM_VALUE_DICT(TERM=other; VALUE=-1; DICT=pairs; DICT_GET=pairs.get; SIGN=+; USIGN=)
            _tmp1094 = pairs.get(other)
            if _tmp1094 is None:
                pairs[other] =  -1
            else:
                _tmp1094 = _tmp1094 + -1
                if _tmp1094:
                    pairs[other] = _tmp1094
                else:
                    del pairs[other]
            #CANONIZE_FACTORS_DICT1(DICT=pairs)
            if not pairs:
                return cls.one
            if len(pairs)==1:
               t, c = pairs.items()[0]
               if c==1:
                   return t
               if t==cls.one:
                   return t
            #RETURN_NEW(HEAD=FACTORS; DATA=pairs)
            #NEWINSTANCE(OBJ=_tmp1108; HEAD=FACTORS; DATA=pairs)
            _tmp1108 = cls(FACTORS, pairs)
            return _tmp1108
        elif rhead is FACTORS:
            #DIV_FACTORS_FACTORS(LHS=self; LHSDATA=ldata; RHS=other; RHSDATA=rdata)
            pairs = ldata.copy()
            pairs_get = pairs.get
            number = 1
            for t,c in rdata.iteritems():
                #MUL_FACTOR_VALUE_DICT(FACTOR=t; SIGN=-; USIGN=-; VALUE=c; DICT=pairs; DICT_GET=pairs_get; NUMBER=number)
                _tmp1129 = pairs_get(t)
                if _tmp1129 is None:
                    pairs[t] = - c
                else:
                    _tmp1129 = _tmp1129 - c
                    if type(_tmp1129) is cls and _tmp1129.head is NUMBER:
                        _tmp1129 = _tmp1129.data
                    if _tmp1129:
                        if t.head is NUMBER:
                            del pairs[t]
                            z, sym = try_power(t.data, _tmp1129)
                            if sym:
                                for t1, c1 in sym:
                                    #NEWINSTANCE(OBJ=tt; HEAD=NUMBER; DATA=t1)
                                    tt = cls(NUMBER, t1)
                                    #ADD_TERM_VALUE_DICT(DICT=pairs; DICT_GET=pairs_get; TERM=tt; VALUE=c1; SIGN=+; USIGN=)
                                    _tmp1143 = pairs_get(tt)
                                    if _tmp1143 is None:
                                        pairs[tt] =  c1
                                    else:
                                        _tmp1143 = _tmp1143 + c1
                                        if _tmp1143:
                                            pairs[tt] = _tmp1143
                                        else:
                                            del pairs[tt]
                            number = number * z
                        else:
                            pairs[t] = _tmp1129
                    else:
                        del pairs[t]
            #CANONIZE_FACTORS_DICT(DICT=pairs; NUMBER=number)
            if not pairs:
                if number is 1:
                    return cls.one
                return number
            if len(pairs)==1:
               t, c = pairs.items()[0]
               if c==1:
                   if number==1:
                       return t
                   #RETURN_NEW(HEAD=TERMS; DATA={t: number})
                   #NEWINSTANCE(OBJ=_tmp1157; HEAD=TERMS; DATA={t: number})
                   _tmp1157 = cls(TERMS, {t: number})
                   return _tmp1157
               if t==cls.one:
                   return number
            if number==1:
                #RETURN_NEW(HEAD=FACTORS; DATA=pairs)
                #NEWINSTANCE(OBJ=_tmp1171; HEAD=FACTORS; DATA=pairs)
                _tmp1171 = cls(FACTORS, pairs)
                return _tmp1171
            #NEWINSTANCE(OBJ=_tmp1122; HEAD=FACTORS; DATA=pairs)
            _tmp1122 = cls(FACTORS, pairs)
            #RETURN_NEW(HEAD=TERMS; DATA={_tmp1122: number})
            #NEWINSTANCE(OBJ=_tmp1192; HEAD=TERMS; DATA={_tmp1122: number})
            _tmp1192 = cls(TERMS, {_tmp1122: number})
            return _tmp1192
        else:
            #DIV_FACTORS_SYMBOL(LHS=self; LHSDATA=ldata; RHS=other; RHSDATA=rdata)
            pairs = ldata.copy()
            #DIV_DICT_SYMBOL(RHS=other; RHSDATA=rdata; DICT=pairs)
            #ADD_TERM_VALUE_DICT(TERM=other; VALUE=-1; DICT=pairs; DICT_GET=pairs.get; SIGN=+; USIGN=)
            _tmp1220 = pairs.get(other)
            if _tmp1220 is None:
                pairs[other] =  -1
            else:
                _tmp1220 = _tmp1220 + -1
                if _tmp1220:
                    pairs[other] = _tmp1220
                else:
                    del pairs[other]
            #CANONIZE_FACTORS_DICT1(DICT=pairs)
            if not pairs:
                return cls.one
            if len(pairs)==1:
               t, c = pairs.items()[0]
               if c==1:
                   return t
               if t==cls.one:
                   return t
            #RETURN_NEW(HEAD=FACTORS; DATA=pairs)
            #NEWINSTANCE(OBJ=_tmp1234; HEAD=FACTORS; DATA=pairs)
            _tmp1234 = cls(FACTORS, pairs)
            return _tmp1234
    else:
        if rhead is NUMBER:
            #DIV_SYMBOL_NUMBER(LHS=self; LHSDATA=ldata; RHS=other; RHSDATA=rdata)
            #DIV_SYMBOL_VALUE(VALUE=rdata; LHS=self; LHSDATA=ldata)
            #MUL_VALUE_SYMBOL(VALUE=div(1, rdata, cls); RHS=self; RHSDATA=ldata)
            _tmp1262 = div(1, rdata, cls)
            if not _tmp1262:
                return cls.zero
            if _tmp1262==1:
                return self
            #RETURN_NEW(HEAD=TERMS; DATA={self: _tmp1262})
            #NEWINSTANCE(OBJ=_tmp1269; HEAD=TERMS; DATA={self: _tmp1262})
            _tmp1269 = cls(TERMS, {self: _tmp1262})
            return _tmp1269
        elif rhead is TERMS:
            #DIV_SYMBOL_TERMS(LHS=self; LHSDATA=ldata; RHS=other; RHSDATA=rdata)
            pairs = rdata
            if len(pairs)==1:
                t,c = pairs.items()[0]
                if self==t:
                    return cls(NUMBER, div(1, c, cls))
                #NEWINSTANCE(OBJ=_tmp1283; HEAD=FACTORS; DATA={self:1, t:-1})
                _tmp1283 = cls(FACTORS, {self:1, t:-1})
                #RETURN_NEW(HEAD=TERMS; DATA={_tmp1283: div(1, c, cls)})
                #NEWINSTANCE(OBJ=_tmp1297; HEAD=TERMS; DATA={_tmp1283: div(1, c, cls)})
                _tmp1297 = cls(TERMS, {_tmp1283: div(1, c, cls)})
                return _tmp1297
            #RETURN_NEW(HEAD=FACTORS; DATA={self:1, other:-1})
            #NEWINSTANCE(OBJ=_tmp1311; HEAD=FACTORS; DATA={self:1, other:-1})
            _tmp1311 = cls(FACTORS, {self:1, other:-1})
            return _tmp1311
        elif rhead is FACTORS:
            #DIV_SYMBOL_FACTORS(LHS=self; LHSDATA=ldata; RHS=other; RHSDATA=rdata)
            pairs = rdata
            if len(pairs)==1:
                t, c = pairs.items()[0]
                if t==self:
                    c = 1 - c
                    if not c:
                        return cls.one
                    if c==1:
                        return t
                    else:
                        #RETURN_NEW(HEAD=FACTORS; DATA={t: c})
                        #NEWINSTANCE(OBJ=_tmp1332; HEAD=FACTORS; DATA={t: c})
                        _tmp1332 = cls(FACTORS, {t: c})
                        return _tmp1332
                #RETURN_NEW(HEAD=FACTORS; DATA={t: -c, self: 1})
                #NEWINSTANCE(OBJ=_tmp1346; HEAD=FACTORS; DATA={t: -c, self: 1})
                _tmp1346 = cls(FACTORS, {t: -c, self: 1})
                return _tmp1346
            #NEG_DICT_VALUES(DICT_IN=rdata; DICT_OUT=pairs)
            pairs = dict([(t, -c) for t,c in rdata.iteritems()])
            #MUL_DICT_SYMBOL(DICT=pairs; RHS=self; RHSDATA=ldata)
            #ADD_TERM_VALUE_DICT(TERM=self; VALUE=1; DICT=pairs; DICT_GET=pairs.get; SIGN=+; USIGN=)
            _tmp1374 = pairs.get(self)
            if _tmp1374 is None:
                pairs[self] =  1
            else:
                _tmp1374 = _tmp1374 + 1
                if _tmp1374:
                    pairs[self] = _tmp1374
                else:
                    del pairs[self]
            #CANONIZE_FACTORS_DICT1(DICT=pairs)
            if not pairs:
                return cls.one
            if len(pairs)==1:
               t, c = pairs.items()[0]
               if c==1:
                   return t
               if t==cls.one:
                   return t
            #RETURN_NEW(HEAD=FACTORS; DATA=pairs)
            #NEWINSTANCE(OBJ=_tmp1388; HEAD=FACTORS; DATA=pairs)
            _tmp1388 = cls(FACTORS, pairs)
            return _tmp1388
        else:
            #DIV_SYMBOL_SYMBOL(LHS=self; LHSDATA=ldata; RHS=other; RHSDATA=rdata)
            if self == other:
                return cls.one
            #RETURN_NEW(HEAD=FACTORS; DATA={self: 1, other: -1})
            #NEWINSTANCE(OBJ=_tmp1409; HEAD=FACTORS; DATA={self: 1, other: -1})
            _tmp1409 = cls(FACTORS, {self: 1, other: -1})
            return _tmp1409
