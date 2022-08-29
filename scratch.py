from typing import TypeVar
T = TypeVar('T')
X = TypeVar('X')

class D:
    @staticmethod
    def foo(x : T) -> T:
        return x 
    
# ALL T . T -> T 
def foo(x : T) -> T:
    return x 

def goo(x : X, t : T) -> tuple[X, T]:
    return x, t 


foo(int)(1)
goo(1, 2)


def boo(x : D) -> D:
    return x 
