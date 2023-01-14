import random
import time
import os

Encrypttimes = 0
key_size = 768

print("----------RSA processor 2.0----------")
print("Author: Jason Yang\n")

CODE_DICT = {
    'A': '1', 'B': '2', 'C': '3', 'D': '4', 'E': '5', 'F': '6', 'G': '7', 
    'H': '8', 'I': '9', 'J': '10', 'K': '11', 'L': '12', 'M': '13', 'N': '14', 
    'O': '15', 'P': '16', 'Q': '17', 'R': '18', 'S': '19', 'T': '20', 
    'U': '21', 'V': '22', 'W': '23', 'X': '24', 'Y': '25', 'Z': '26', 

    'a': '27', 'b': '28', 'c': '29', 'd': '30', 'e': '31', 'f': '32', 'g': '33', 
    'h': '34', 'i': '35', 'j': '36', 'k': '37', 'l': '38', 'm': '39', 'n': '40', 
    'o': '41', 'p': '42', 'q': '43', 'r': '44', 's': '45', 't': '46', 
    'u': '47', 'v': '48', 'w': '49', 'x': '50', 'y': '51', 'z': '52', 
    
    '0': '53', '1': '54', '2': '55', '3': '56', '4': '57', 
    '5': '58', '6': '59', '7': '60', '8': '61', '9': '62', 

    '`': '63', '~': '64', '!': '65', '@': '66', '#': '67', '$': '68', '%': '69', '^':'70', 
    '&': '71', '*': '72', '(': '73', ')': '74', '-': '75', 
    '_': '76', '=': '77', '+': '78', '[': '79', ']': '80', 
    '{': '81', '}': '82', '\\': '83', '|': '84', ';': '85', 
    ':': '86', "'": '87', '"': '88', ',': '89', '<': '90', 
    '.': '91', '>': '92', '/': '93', '?': '94', ' ': '95', 
}

INVERSE_CODE_DICT = {v: k for k, v in CODE_DICT.items()}

# 求最大公因数
def gcd(a, b):
    if a < b:
        return gcd(b, a)
    elif a % b == 0:
        return b
    else:
        return gcd(b, a % b)


# 快速幂+取模
def power(a, b, c):
    ans = 1
    while b != 0:
        if b & 1:
            ans = (ans * a) % c
        b >>= 1
        a = (a * a) % c
    return ans


# 快速幂
def quick_power(a: int, b: int) -> int:
    ans = 1
    while b != 0:
        if b & 1:
            ans = ans * a
        b >>= 1
        a = a * a
    return ans


# 大质数检测
def Miller_Rabin(n):
    a = random.randint(2, n - 2)  # 随机第选取一个a∈[2,n-2]
    # print("随机选取的a=%lld\n"%a)
    s = 0  # s为d中的因子2的幂次数。
    d = n - 1
    while (d & 1) == 0:  # 将d中因子2全部提取出来。
        s += 1
        d >>= 1

    x = power(a, d, n)
    for i in range(s):  # 进行s次二次探测
        newX = power(x, 2, n)
        if newX == 1 and x != 1 and x != n - 1:
            return False  # 用二次定理的逆否命题，此时n确定为合数。
        x = newX

    if x != 1:  # 用费马小定理的逆否命题判断，此时x=a^(n-1) (mod n)，那么n确定为合数。
        return False

    return True  # 用费马小定理的逆命题判断。能经受住考验至此的数，大概率为素数。


# 卢卡斯-莱墨素性检验
def Lucas_Lehmer(num: int) -> bool:  # 快速检验pow(2,m)-1是不是素数
    if num == 2:
        return True
    if num % 2 == 0:
        return False
    s = 4
    Mersenne = pow(2, num) - 1  # pow(2, num)-1是梅森数
    for x in range(1, (num - 2) + 1):  # num-2是循环次数，+1表示右区间开
        s = ((s * s) - 2) % Mersenne
    if s == 0:
        return True
    else:
        return False


# 扩展的欧几里得算法，ab=1 (mod m), 得到a在模m下的乘法逆元b
def Extended_Eulid(a: int, m: int) -> int:
    def extended_eulid(a: int, m: int):
        if a == 0:  # 边界条件
            return 1, 0, m
        else:
            x, y, gcd = extended_eulid(m % a, a)  # 递归
            x, y = y, (x - (m // a) * y)  # 递推关系，左端为上层
            return x, y, gcd  # 返回第一层的计算结果。
        # 最终返回的y值即为b在模a下的乘法逆元
        # 若y为复数，则y+a为相应的正数逆元

    n = extended_eulid(a, m)
    if n[1] < 0:
        return n[1] + m
    else:
        return n[1]


# 按照需要的bit来生成大素数
def Generate_prime(key_size: int) -> int:
    while True:
        num = random.randrange(quick_power(2, key_size - 1), quick_power(2, key_size))
        if Miller_Rabin(num):
            return num


# 生成公钥和私钥
def KeyGen(p: int, q: int):
    e = random.randint(1, (p - 1) * (q - 1))
    while gcd(e, (p - 1) * (q - 1)) != 1:
        e = random.randint(1, (p - 1) * (q - 1))
    n = p * q
    d = Extended_Eulid(e, (p - 1) * (q - 1))
    return n, e, d


def Encrypt(message: int, e: int, n: int) -> int:
    ciphertext = power(message, e, n)
    return ciphertext


def Decrypt(ciphertext: int, d: int, n: int) -> int:
    plaintext = power(ciphertext, d, n)
    return plaintext

def rsa_encrypt_generate_key():
    print("\nGenerating new RSA_key...")
    global key_size
    global p 
    global q 
    global n 
    global e 
    global d
    p = Generate_prime(key_size)
    q = Generate_prime(key_size)
    n, e, d = KeyGen(p, q)
    print("finished!")


def strToCn(str_unicode):
    str_byte =  bytes(str_unicode, encoding = "utf8")
    str_byte_unicode = str_byte.decode("unicode_escape")
    return str_byte_unicode

def rsa_decrypt_data():
    global chipertext
    global d 
    global n 
    global message 
    global t
    chipertext = int(input("\nEnter the encrypted message >>>  "))
    d = int(input("Enter the private key_d >>>  "))
    n = int(input("Enter the private key_n >>>  "))
    message = str(Decrypt(chipertext, d, n))
    lists = message.split("100")
    t = ''
    print("\n------Decrypt data------")
    while '' in lists:
        lists.remove('')
    for code in lists:
        t += INVERSE_CODE_DICT[code] + ''
    print(strToCn(t))
    print("\n---------END----------\n")
    os.system('pause')
    choose_mode()

def rsa_encrypt_process_choose_mode_1():
    global message
    global ciphertext
    global result
    global key_size
    global e
    global n
    global Encrypttimes
    print("\nCHOOSE the processing mode:\n<1> <<<Back to HOME PAGE\n<2> Continue encrypt more data use the same RSA_key\n<3> Generate a new RSA_key to encrypt data\n<4> Enter the public key to encrypt data\n<5> SETTING for Encryption")
    mode = int(input("Please enter the MODE>>>  "))
    if mode == 1:
        choose_mode()
    elif mode == 2:
        rsa_encrypt_data()
    elif mode == 3:
        rsa_encrypt_generate_key()
        rsa_encrypt_data()
    elif mode == 4:
        e = int(input("\nEnter the public key_e >>>  "))
        n = int(input("Enter the public key_n >>>  "))
        message = input("\nEncrypt data>>>\n")
        message = message.encode('unicode-escape').decode()
        t = ' '
        for letter in message:
            if letter != ' ':
                t += CODE_DICT[letter] + ' '
            else:
                t += ' '
        result = t.replace(' ', '100')
        message = int(result)
        # 公钥加密
        ciphertext = Encrypt(message, e, n)
        Encrypttimes = Encrypttimes + 1
        print("\n------Public Key------")
        print("N>>>", n)
        print("\nE>>>", e)
        print("---------END----------\n")
        print("------Encrypt data------")
        print(ciphertext)
        print("---------END----------\n")
        print("WARN! >>> We cannot ensure the encrypt process is correct \nas the RSA_key_size may too small or the encrypt data is too large. \n")
        os.system('pause')
        rsa_encrypt_process_choose_mode_1()
    elif mode == 5: 
        def rsa_encrypt_setting_mode():
            settingtimes = 0
            global key_size
            print("\nCHOOSE the processing mode:\n<1> <<<Back to Encryption PAGE\n<2> Setting for RSA_key_size")
            mode = int(input("Please enter the MODE>>>  "))
            if mode == 1:
                if settingtimes == 0:
                    rsa_encrypt_process_choose_mode_2()
                else:
                    rsa_encrypt_process_choose_mode_1()
            if mode == 2:
                def enter_new_key_size():
                    global keysizenew
                    global key_size
                    keysizenew = int(input("\nPlease enter new RSA_key_size>>>  "))
                enter_new_key_size()
                if keysizenew < 10:
                    print("ERROR!\nThe key size is too small!")
                    enter_new_key_size()
                elif keysizenew > 768:
                    print("ERROR!\nThe key size is too large!")
                    enter_new_key_size()
                else:
                    key_size = keysizenew
                    print("SETTING DONE! keysize>>>", key_size, "bit\n")
                    settingtimes = settingtimes + 1
                os.system('pause')
                rsa_encrypt_setting_mode()
        rsa_encrypt_setting_mode()

def rsa_encrypt_process_choose_mode_2():
    global message
    global ciphertext
    global result
    global key_size
    global e
    global n
    global Encrypttimes
    print("\nCHOOSE the processing mode:\n<1> <<<Back to HOME PAGE\n<2> Generate a new RSA_key to encrypt data\n<3> Enter the public key to encrypt data\n<4> SETTING for Encryption")
    mode = int(input("Please enter the MODE>>>  "))
    if mode == 1:
        choose_mode()
    elif mode == 2:
        rsa_encrypt_generate_key()
        rsa_encrypt_data()
    elif mode == 3:
        e = int(input("\nEnter the public key_e >>>  "))
        n = int(input("Enter the public key_n >>>  "))
        message = input("\nEncrypt data>>>\n")
        message = message.encode('unicode-escape').decode()
        t = ' '
        for letter in message:
            if letter != ' ':
                t += CODE_DICT[letter] + ' '
            else:
                t += ' '
        result = t.replace(' ', '100')
        message = int(result)
        # 公钥加密
        ciphertext = Encrypt(message, e, n)
        Encrypttimes = Encrypttimes + 1
        print("\n------Public Key------")
        print("N>>>", n)
        print("\nE>>>", e)
        print("---------END----------\n")
        print("------Encrypt data------")
        print(ciphertext)
        print("---------END----------\n")
        print("WARN! >>> We cannot ensure the encrypt process is correct \nas the RSA_key_size may too small or the encrypt data is too large. \n")
        os.system('pause')
        rsa_encrypt_process_choose_mode_1()
    elif mode == 4: 
        def rsa_encrypt_setting_mode():
            settingtimes = 0
            global key_size
            print("\nCHOOSE the processing mode:\n<1> <<<Back to Encryption PAGE\n<2> Setting for RSA_key_size")
            mode = int(input("Please enter the MODE>>>  "))
            if mode == 1:
                if settingtimes == 0:
                    rsa_encrypt_process_choose_mode_2()
                else:
                    rsa_encrypt_process_choose_mode_1()
            if mode == 2:
                def enter_new_key_size():
                    global keysizenew
                    global key_size
                    keysizenew = int(input("\nPlease enter new RSA_key_size>>>  "))
                enter_new_key_size()
                if keysizenew < 10:
                    print("ERROR!\nThe key size is too small!")
                    enter_new_key_size()
                elif keysizenew > 768:
                    print("ERROR!\nThe key size is too large!")
                    enter_new_key_size()
                else:
                    key_size = keysizenew
                    print("SETTING DONE! keysize>>>", key_size, "bit\n")
                    settingtimes = settingtimes + 1
                os.system('pause')
                rsa_encrypt_setting_mode()
        rsa_encrypt_setting_mode()

def rsa_encrypt_data():
    global message
    global ciphertext
    global plaintext
    global result
    global e
    global n
    global d
    message = input("\nEncrypt data>>>\n")
    message = message.encode('unicode-escape').decode()
    t = ' '
    for letter in message:
        if letter != ' ':
            t += CODE_DICT[letter] + ' '
        else:
            t += ' '
    result = t.replace(' ', '100')
    message = int(result)
    # 公钥加密
    ciphertext = Encrypt(message, e, n)
    # 私钥解密
    plaintext = Decrypt(ciphertext, d, n)
    rsa_output()

def rsa_encrypt_process():
    global Encrypttimes
    global e
    global n
    global d
    global key_size
    # 消息
    
    if Encrypttimes == 0:
        rsa_encrypt_process_choose_mode_2()
    else:
        rsa_encrypt_process_choose_mode_1()

def rsa_output():
    global message
    global ciphertext
    global plaintext
    global result
    global e
    global n
    global d
    global Encrypttimes
    if message == plaintext:
        Encrypttimes = Encrypttimes + 1
        print("\nEncrypted data: Morse>>>\n", result)
        print("\nEncrypted data: RSA>>>")
        print("Key size>>>", key_size, "bit")
        print("-------Private Key-------")
        print("N>>>", n)
        print("\nd>>>", d)
        print("---------END----------\n\n")
        print("------Public Key------")
        print("N>>>", n)
        print("\nE>>>", e)
        print("---------END----------\n")
        print("------Encrypt data------")
        print(ciphertext)
        print("---------END----------\n")
        print("------Decrypt data------")
        print("Plaintext:  ", plaintext)
        print("---------END----------\n")
        os.system('pause')
        rsa_encrypt_process_choose_mode_1()

    else:
        def prl():
            pr = input("Printed Error log？（Y/N）")
            if pr == "Y":
                print("\nEncrypted data: Morse>>>\n", result)
                print("\nEncrypted data: RSA>>>")
                print("Key size>>>", key_size, "bit")
                print("-------Private Key-------")
                print("N>>>", n)
                print("\nd>>>", d)
                print("---------END----------\n\n")
                print("------Public Key------")
                print("N>>>", n)
                print("\nE>>>", e)
                print("---------END----------\n")
                print("------Encrypt data------")
                print(ciphertext)
                print("---------END----------\n")
                print("------Decrypt data------")
                print("Plaintext:  ", plaintext)
                print("---------END----------\n")
        print("\nError!\nYou entered an oversized encrypted data or a too small RSA_key_size!")
        prl()
        os.system('pause')
        rsa_encrypt_process_choose_mode_1()

def choose_mode():
    print("\nCHOOSE the processing mode:\n<1> encryption\n<2> decryption\n<3> EXIT")
    mode = int(input("Please enter the MODE>>>  "))
    if mode == 1:
        rsa_encrypt_process()
    elif mode == 2:
        rsa_decrypt_data()
    elif mode == 3:
        print("\nThank you for using RSA processor!")
        print("Author: Jason Yang\n")
        time.sleep(0.7)
        print ('exiting...')
        time.sleep(3)
        exit ()

os.system('pause')
choose_mode()