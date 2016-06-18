Y = lambda f: (lambda t: t(t))(lambda h: lambda *args: f(h(h))(*args))
fac = lambda f: lambda n: (1 if (n == 0) else n*f(n-1))
