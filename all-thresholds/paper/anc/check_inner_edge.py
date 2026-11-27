"""Independent exact sign checks in the original ordered rows near the critical value."""
from decimal import Decimal as D, getcontext
from fractions import Fraction
from math import comb, factorial
import json

getcontext().prec = 85
pi = D("3.141592653589793238462643383279502884197169399375105820974944592")
def critical(j):
    lo, hi = D(2).ln(), D(2)
    def tail(x, k):
        return x.exp() - sum(x**i / factorial(i) for i in range(k))
    for _ in range(205):
        x = (lo + hi)/2
        if 2*tail(x,j)*factorial(j-1)/x**(j-1) > x.exp()-2:
            lo = x
        else:
            hi = x
    a=(lo+hi)/2
    b=tail(a,j)
    c=(a.exp()-2)/b
    scale=a*a*(-a.exp()+c*tail(a,j-2))/(2*b)
    return a,c,scale

def rows(j, limit):
    history=[[1]]
    for n in range(1,limit+1):
        row=[0]*(n//j+1)
        for s in range(1,n+1):
            v=comb(n,s); mark=int(s>=j)
            for h,a in enumerate(history[n-s]):
                row[h+mark]+=a*v
        history.append(row)
    return history

def sign(row, t):
    value=0; denpower=1
    for a in reversed(row):
        value=value*t.numerator+a*denpower
        denpower*=t.denominator
    return (value>0)-(value<0)

def main():
    output=[]
    for j in (2,3,4,6,8):
        a,c,L=critical(j)
        pol=rows(j,256)
        record=dict(j=j,alpha=str(a),critical_radius=str(c),scale=str(L),sign_brackets=[])
        for n in (64,128,256):
            for k in (1,2):
                pair=[]
                for u in (D(k)-D("0.25"),D(k)+D("0.25")):
                    t=1-c-L*(pi*u/n)**2
                    t=Fraction(round(t*2**55),2**55)
                    pair.append(dict(t=str(t),sign=sign(pol[n],t)))
                opposite = pair[0]["sign"] * pair[1]["sign"] < 0
                assert opposite, (j, n, k, pair)
                record["sign_brackets"].append(dict(n=n,k=k,opposite=opposite,endpoints=pair))
        output.append(record)
    print(json.dumps(output,indent=2))
if __name__=="__main__":
    main()
