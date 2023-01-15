import random
import time
import os
import re

Encrypttimes = 0 #加密次数归零
key_size = 768 #预设密钥长度

#客户端显示
print("----------RSA processor 2.0----------")
print("Copyright©2023 Yang Jiepeng") #版权声明
print("This program is released under GNU GENERAL PUBLIC LICENSE\n") #许可证声明

#ANSCII加密字典
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

#ANSCII解密字典
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

#通过RSA加密消息
def Encrypt(message: int, e: int, n: int) -> int:
    ciphertext = power(message, e, n)
    return ciphertext

#通过RSA解密消息
def Decrypt(ciphertext: int, d: int, n: int) -> int:
    plaintext = power(ciphertext, d, n)
    return plaintext

#生成密钥
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
    print("finished!\n")

#将str字符串转换成byte形式 反斜杠转义
def strToCn(str_unicode):
    str_byte =  bytes(str_unicode, encoding = "utf8")
    str_byte_unicode = str_byte.decode("unicode_escape")
    return str_byte_unicode

#解密消息
def rsa_decrypt_data():
    global chipertext
    global d 
    global n 
    global message 
    global t
    def enter_chipertext():
        global chipertext
        chipertext = input("Enter the encrypted message >>>  ")
        if chipertext == "":
            enter_chipertext()
    chipertext = input("\nEnter the encrypted message >>>  ")
    if chipertext == "":
        enter_chipertext()
    chipertext = int(chipertext)
    def en_d():
        global d
        d = (input("Enter the private key_d >>>  "))
        if d == "":
            en_d()
    en_d()
    d = int(d)
    def en_n():
        global n
        n = input("Enter the private key_n >>>  ")
        if n == "":
            en_n()
    en_n()
    n = int(n)
    #通过RSA解密消息
    message = str(Decrypt(chipertext, d, n))
    #分割字符串
    pattern = re.compile('.{2}')
    message = '100'.join(pattern.findall(message))
    lists = message.split("100")
    t = ''
    print("\n------Decrypt data------")
    while '' in lists:
        lists.remove('')
    #通过ANSCII解密字典解密
    for code in lists:
        t += INVERSE_CODE_DICT[code] + ''
    #通过unicode解密
    print(strToCn(t))
    print("\n---------END----------\n")
    os.system('pause')
    choose_mode()

#客户端反馈
def rsa_encrypt_process_choose_mode_1():
    global message
    global ciphertext
    global result
    global key_size
    global e
    global n
    global Encrypttimes
    global settingtimes
    print("\nCHOOSE the processing mode:\n<1> <<<Back to HOME PAGE\n<2> Continue encrypt more data use the same RSA_key\n<3> Generate a new RSA_key to encrypt data\n<4> Enter the public key to encrypt data\n<5> SETTING for Encryption")
    def en_choose_mode_1():
        global message
        global ciphertext
        global result
        global key_size
        global e
        global n
        global Encrypttimes
        global settingtimes
        mode = input("Please enter the MODE>>>  ")
        if mode == "1":
            choose_mode()
        elif mode == "2":
            rsa_encrypt_data()
        elif mode == "3":
            rsa_encrypt_generate_key()
            rsa_encrypt_data()
        elif mode == "4":
            e = input("\nEnter the public key_e >>>  ")
            def enter_e():
                global e
                e = input("Enter the public key_e >>>  ")
                if e == "":
                    enter_e()
            if e == "":
                enter_e()
            e = int(e)
            def enter_n():
                global n
                n = input("Enter the public key_n >>>  ")
                if n == "":
                    enter_n()
            enter_n()
            n = int(n)
            def message_enter():
                global message
                message = input("Encrypt data>>>")
                if message == "":
                    message_enter()
            message_enter()
            message = message.encode('unicode-escape').decode()
            t = ' '
            for letter in message:
                if letter != ' ':
                    t += CODE_DICT[letter] + ' '
                else:
                    t += ' '
            result = t.replace(' ', '')
            message = int(result)
            # 公钥加密
            ciphertext = Encrypt(message, e, n)
            print("\n------Public Key------")
            print("N>>>", n)
            print("\nE>>>", e)
            print("---------END----------\n")
            print("------Encrypt data------")
            print(ciphertext)
            print("---------END----------\n")
            print("WARN! >>> We cannot ensure the encrypt process is correct \nas the RSA_key_size may too small or the encrypt data is too large. \n")
            os.system('pause')
            rsa_encrypt_process()
        elif mode == "5": 
            settingtimes = 0
            def rsa_encrypt_setting_mode():
                global key_size
                print("\nCHOOSE the processing mode:\n<1> <<<Back to Encryption PAGE\n<2> Setting for RSA_key_size")
                def enter_mode():
                    global key_size
                    mode = input("Please enter the MODE>>>  ")
                    if mode == "1":
                        rsa_encrypt_process_choose_mode_1()
                    if mode == "2":
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
                        os.system('pause')
                        rsa_encrypt_process_choose_mode_2()
                    else:
                        enter_mode()
                enter_mode()
            rsa_encrypt_setting_mode()
        else:
            en_choose_mode_1()
    en_choose_mode_1()

#客户端反馈
def rsa_encrypt_process_choose_mode_2():
    global message
    global ciphertext
    global result
    global key_size
    global e
    global n
    global Encrypttimes
    print("\nCHOOSE the processing mode:\n<1> <<<Back to HOME PAGE\n<2> Generate a new RSA_key to encrypt data\n<3> Enter the public key to encrypt data\n<4> SETTING for Encryption")
    def en_choose_mode_2():
        global message
        global ciphertext
        global result
        global key_size
        global e
        global n
        global Encrypttimes
        mode = input("Please enter the MODE>>>  ")
        if mode == "1":
            choose_mode()
        elif mode == "2":
            rsa_encrypt_generate_key()
            rsa_encrypt_data()
        elif mode == "3":
            e = input("\nEnter the public key_e >>>  ")
            def enter_e():
                global e
                e = input("Enter the public key_e >>>  ")
                if e == "":
                    enter_e()
            if e == "":
                enter_e()
            e = int(e)
            def enter_n():
                global n
                n = input("Enter the public key_n >>>  ")
                if n == "":
                    enter_n()
            enter_n()
            n = int(n)
            def message_enter():
                global message
                message = input("Encrypt data>>>")
                if message == "":
                    message_enter()
            message_enter()
            message = message.encode('unicode-escape').decode()
            t = ' '
            for letter in message:
                if letter != ' ':
                    t += CODE_DICT[letter] + ' '
                else:
                    t += ' '
            result = t.replace(' ', '')
            message = int(result)
            # 公钥加密
            ciphertext = Encrypt(message, e, n)
            print("\n------Public Key------")
            print("N>>>", n)
            print("\nE>>>", e)
            print("---------END----------\n")
            print("------Encrypt data------")
            print(ciphertext)
            print("---------END----------\n")
            print("WARN! >>> We cannot ensure the encrypt process is correct \nas the RSA_key_size may too small or the encrypt data is too large. \n")
            os.system('pause')
            rsa_encrypt_process()
        elif mode == "4": 
            def rsa_encrypt_setting_mode():
                global key_size
                print("\nCHOOSE the processing mode:\n<1> <<<Back to Encryption PAGE\n<2> Setting for RSA_key_size")
                def enter_mode():
                    global key_size
                    mode = input("Please enter the MODE>>>  ")
                    if mode == "1":
                            rsa_encrypt_process_choose_mode_2()
                    if mode == "2":
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
                        os.system('pause')
                        rsa_encrypt_setting_mode()
                    else:
                        enter_mode()
                enter_mode()
            rsa_encrypt_setting_mode()
        else:
            en_choose_mode_2()
    en_choose_mode_2()

#加密消息
def rsa_encrypt_data():
    global message
    global ciphertext
    global plaintext
    global result
    global e
    global n
    global d
    message = ""
    def message_enter():
        global message
        message = input("Encrypt data>>>")
        if message == "":
            message_enter()
    message_enter()
    #通过unicode加密
    message = message.encode('unicode-escape').decode()
    t = ' '
    #通过ANSCII字典加密
    for letter in message:
        if letter != ' ':
            t += CODE_DICT[letter] + ' '
        else:
            t += ' '
    result = t.replace(' ', '')
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

#输出
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

#客户端反馈
def choose_mode():
    print("\nCHOOSE the processing mode:\n<1> encryption\n<2> decryption\n<3> Python code\n<4> LICENSE\n<5> EXIT")
    def choose_mode_1():
        mode = input("Please enter the MODE>>>  ")
        if mode == "1":
            rsa_encrypt_process()
        elif mode == "2":
            rsa_decrypt_data()
        elif mode == "3":
            print("\n")
            a = r"import random/nimport time/nimport os/nimport re/n/nEncrypttimes = 0 #加密次数归零/nkey_size = 768 #预设密钥长度/n/n#客户端显示/nprint(‘----------RSA processor 2.0----------’)/nprint(‘Copyright©2023 Yang Jiepeng’) #版权声明/nprint(‘This program is released under GNU GENERAL PUBLIC LICENSE\n’) #许可证声明/n/n#ANSCII加密字典/nCODE_DICT = {/n    'A': '1', 'B': '2', 'C': '3', 'D': '4', 'E': '5', 'F': '6', 'G': '7', /n    'H': '8', 'I': '9', 'J': '10', 'K': '11', 'L': '12', 'M': '13', 'N': '14', /n    'O': '15', 'P': '16', 'Q': '17', 'R': '18', 'S': '19', 'T': '20', /n    'U': '21', 'V': '22', 'W': '23', 'X': '24', 'Y': '25', 'Z': '26', /n/n    'a': '27', 'b': '28', 'c': '29', 'd': '30', 'e': '31', 'f': '32', 'g': '33', /n    'h': '34', 'i': '35', 'j': '36', 'k': '37', 'l': '38', 'm': '39', 'n': '40', /n    'o': '41', 'p': '42', 'q': '43', 'r': '44', 's': '45', 't': '46', /n    'u': '47', 'v': '48', 'w': '49', 'x': '50', 'y': '51', 'z': '52', /n    /n    '0': '53', '1': '54', '2': '55', '3': '56', '4': '57', /n    '5': '58', '6': '59', '7': '60', '8': '61', '9': '62', /n/n    '`': '63', '~': '64', '!': '65', '@': '66', '#': '67', '$': '68', '%': '69', '^':'70', /n    '&': '71', '*': '72', '(': '73', ')': '74', '-': '75', /n    '_': '76', '=': '77', '+': '78', '[': '79', ']': '80', /n    '{': '81', '}': '82', '\\': '83', '|': '84', ';': '85', /n    ':': '86', ‘'‘: '87', '‘': '88', ',': '89', '<': '90', /n    '.': '91', '>': '92', '/': '93', '?': '94', ' ': '95', /n}/n/n#ANSCII解密字典/nINVERSE_CODE_DICT = {v: k for k, v in CODE_DICT.items()}/n/n# 求最大公因数/ndef gcd(a, b):/n    if a < b:/n        return gcd(b, a)/n    elif a % b == 0:/n        return b/n    else:/n        return gcd(b, a % b)/n/n/n# 快速幂+取模/ndef power(a, b, c):/n    ans = 1/n    while b != 0:/n        if b & 1:/n            ans = (ans * a) % c/n        b >>= 1/n        a = (a * a) % c/n    return ans/n/n/n# 快速幂/ndef quick_power(a: int, b: int) -> int:/n    ans = 1/n    while b != 0:/n        if b & 1:/n            ans = ans * a/n        b >>= 1/n        a = a * a/n    return ans/n/n/n# 大质数检测/ndef Miller_Rabin(n):/n    a = random.randint(2, n - 2)  # 随机第选取一个a∈[2,n-2]/n    # print(‘随机选取的a=%lld\n’%a)/n    s = 0  # s为d中的因子2的幂次数。/n    d = n - 1/n    while (d & 1) == 0:  # 将d中因子2全部提取出来。/n        s += 1/n        d >>= 1/n/n    x = power(a, d, n)/n    for i in range(s):  # 进行s次二次探测/n        newX = power(x, 2, n)/n        if newX == 1 and x != 1 and x != n - 1:/n            return False  # 用二次定理的逆否命题，此时n确定为合数。/n        x = newX/n/n    if x != 1:  # 用费马小定理的逆否命题判断，此时x=a^(n-1) (mod n)，那么n确定为合数。/n        return False/n/n    return True  # 用费马小定理的逆命题判断。能经受住考验至此的数，大概率为素数。/n/n/n# 卢卡斯-莱墨素性检验/ndef Lucas_Lehmer(num: int) -> bool:  # 快速检验pow(2,m)-1是不是素数/n    if num == 2:/n        return True/n    if num % 2 == 0:/n        return False/n    s = 4/n    Mersenne = pow(2, num) - 1  # pow(2, num)-1是梅森数/n    for x in range(1, (num - 2) + 1):  # num-2是循环次数，+1表示右区间开/n        s = ((s * s) - 2) % Mersenne/n    if s == 0:/n        return True/n    else:/n        return False/n/n/n# 扩展的欧几里得算法，ab=1 (mod m), 得到a在模m下的乘法逆元b/ndef Extended_Eulid(a: int, m: int) -> int:/n    def extended_eulid(a: int, m: int):/n        if a == 0:  # 边界条件/n            return 1, 0, m/n        else:/n            x, y, gcd = extended_eulid(m % a, a)  # 递归/n            x, y = y, (x - (m // a) * y)  # 递推关系，左端为上层/n            return x, y, gcd  # 返回第一层的计算结果。/n        # 最终返回的y值即为b在模a下的乘法逆元/n        # 若y为复数，则y+a为相应的正数逆元/n/n    n = extended_eulid(a, m)/n    if n[1] < 0:/n        return n[1] + m/n    else:/n        return n[1]/n/n/n# 按照需要的bit来生成大素数/ndef Generate_prime(key_size: int) -> int:/n    while True:/n        num = random.randrange(quick_power(2, key_size - 1), quick_power(2, key_size))/n        if Miller_Rabin(num):/n            return num/n/n/n# 生成公钥和私钥/ndef KeyGen(p: int, q: int):/n    e = random.randint(1, (p - 1) * (q - 1))/n    while gcd(e, (p - 1) * (q - 1)) != 1:/n        e = random.randint(1, (p - 1) * (q - 1))/n    n = p * q/n    d = Extended_Eulid(e, (p - 1) * (q - 1))/n    return n, e, d/n/n#通过RSA加密消息/ndef Encrypt(message: int, e: int, n: int) -> int:/n    ciphertext = power(message, e, n)/n    return ciphertext/n/n#通过RSA解密消息/ndef Decrypt(ciphertext: int, d: int, n: int) -> int:/n    plaintext = power(ciphertext, d, n)/n    return plaintext/n/n#生成密钥/ndef rsa_encrypt_generate_key():/n    print(‘\nGenerating new RSA_key...’)/n    global key_size/n    global p /n    global q /n    global n /n    global e /n    global d/n    p = Generate_prime(key_size)/n    q = Generate_prime(key_size)/n    n, e, d = KeyGen(p, q)/n    print(‘finished!\n’)/n/n#将str字符串转换成byte形式 反斜杠转义/ndef strToCn(str_unicode):/n    str_byte =  bytes(str_unicode, encoding = ‘utf8’)/n    str_byte_unicode = str_byte.decode(‘unicode_escape’)/n    return str_byte_unicode/n/n#解密消息/ndef rsa_decrypt_data():/n    global chipertext/n    global d /n    global n /n    global message /n    global t/n    def enter_chipertext():/n        global chipertext/n        chipertext = input(‘Enter the encrypted message >>>  ‘)/n        if chipertext == ‘‘:/n            enter_chipertext()/n    chipertext = input(‘\nEnter the encrypted message >>>  ‘)/n    if chipertext == ‘‘:/n        enter_chipertext()/n    chipertext = int(chipertext)/n    def en_d():/n        global d/n        d = (input(‘Enter the private key_d >>>  ‘))/n        if d == ‘‘:/n            en_d()/n    en_d()/n    d = int(d)/n    def en_n():/n        global n/n        n = input(‘Enter the private key_n >>>  ‘)/n        if n == ‘‘:/n            en_n()/n    en_n()/n    n = int(n)/n    #通过RSA解密消息/n    message = str(Decrypt(chipertext, d, n))/n    #分割字符串/n    pattern = re.compile('.{2}')/n    message = '100'.join(pattern.findall(message))/n    lists = message.split(‘100’)/n    t = ''/n    print(‘\n------Decrypt data------’)/n    while '' in lists:/n        lists.remove('')/n    #通过ANSCII解密字典解密/n    for code in lists:/n        t += INVERSE_CODE_DICT[code] + ''/n    #通过unicode解密/n    print(strToCn(t))/n    print(‘\n---------END----------\n’)/n    os.system('pause')/n    choose_mode()/n/n#客户端反馈/ndef rsa_encrypt_process_choose_mode_1():/n    global message/n    global ciphertext/n    global result/n    global key_size/n    global e/n    global n/n    global Encrypttimes/n    global settingtimes/n    print(‘\nCHOOSE the processing mode:\n<1> <<<Back to HOME PAGE\n<2> Continue encrypt more data use the same RSA_key\n<3> Generate a new RSA_key to encrypt data\n<4> Enter the public key to encrypt data\n<5> SETTING for Encryption’)/n    def en_choose_mode_1():/n        global message/n        global ciphertext/n        global result/n        global key_size/n        global e/n        global n/n        global Encrypttimes/n        global settingtimes/n        mode = input(‘Please enter the MODE>>>  ‘)/n        if mode == ‘1’:/n            choose_mode()/n        elif mode == ‘2’:/n            rsa_encrypt_data()/n        elif mode == ‘3’:/n            rsa_encrypt_generate_key()/n            rsa_encrypt_data()/n        elif mode == ‘4’:/n            e = input(‘\nEnter the public key_e >>>  ‘)/n            def enter_e():/n                global e/n                e = input(‘Enter the public key_e >>>  ‘)/n                if e == ‘‘:/n                    enter_e()/n            if e == ‘‘:/n                enter_e()/n            e = int(e)/n            def enter_n():/n                global n/n                n = input(‘Enter the public key_n >>>  ‘)/n                if n == ‘‘:/n                    enter_n()/n            enter_n()/n            n = int(n)/n            def message_enter():/n                global message/n                message = input(‘Encrypt data>>>‘)/n                if message == ‘‘:/n                    message_enter()/n            message_enter()/n            message = message.encode('unicode-escape').decode()/n            t = ' '/n            for letter in message:/n                if letter != ' ':/n                    t += CODE_DICT[letter] + ' '/n                else:/n                    t += ' '/n            result = t.replace(' ', '')/n            message = int(result)/n            # 公钥加密/n            ciphertext = Encrypt(message, e, n)/n            print(‘\n------Public Key------’)/n            print(‘N>>>‘, n)/n            print(‘\nE>>>‘, e)/n            print(‘---------END----------\n’)/n            print(‘------Encrypt data------’)/n            print(ciphertext)/n            print(‘---------END----------\n’)/n            print(‘WARN! >>> We cannot ensure the encrypt process is correct \nas the RSA_key_size may too small or the encrypt data is too large. \n’)/n            os.system('pause')/n            rsa_encrypt_process()/n        elif mode == ‘5’: /n            settingtimes = 0/n            def rsa_encrypt_setting_mode():/n                global key_size/n                print(‘\nCHOOSE the processing mode:\n<1> <<<Back to Encryption PAGE\n<2> Setting for RSA_key_size’)/n                def enter_mode():/n                    global key_size/n                    mode = input(‘Please enter the MODE>>>  ‘)/n                    if mode == ‘1’:/n                        rsa_encrypt_process_choose_mode_1()/n                    if mode == ‘2’:/n                        def enter_new_key_size():/n                            global keysizenew/n                            global key_size/n                            keysizenew = int(input(‘\nPlease enter new RSA_key_size>>>  ‘))/n                        enter_new_key_size()/n                        if keysizenew < 10:/n                            print(‘ERROR!\nThe key size is too small!’)/n                            enter_new_key_size()/n                        elif keysizenew > 768:/n                            print(‘ERROR!\nThe key size is too large!’)/n                            enter_new_key_size()/n                        else:/n                            key_size = keysizenew/n                            print(‘SETTING DONE! keysize>>>‘, key_size, ‘bit\n’)/n                        os.system('pause')/n                        rsa_encrypt_process_choose_mode_2()/n                    else:/n                        enter_mode()/n                enter_mode()/n            rsa_encrypt_setting_mode()/n        else:/n            en_choose_mode_1()/n    en_choose_mode_1()/n/n#客户端反馈/ndef rsa_encrypt_process_choose_mode_2():/n    global message/n    global ciphertext/n    global result/n    global key_size/n    global e/n    global n/n    global Encrypttimes/n    print(‘\nCHOOSE the processing mode:\n<1> <<<Back to HOME PAGE\n<2> Generate a new RSA_key to encrypt data\n<3> Enter the public key to encrypt data\n<4> SETTING for Encryption’)/n    def en_choose_mode_2():/n        global message/n        global ciphertext/n        global result/n        global key_size/n        global e/n        global n/n        global Encrypttimes/n        mode = input(‘Please enter the MODE>>>  ‘)/n        if mode == ‘1’:/n            choose_mode()/n        elif mode == ‘2’:/n            rsa_encrypt_generate_key()/n            rsa_encrypt_data()/n        elif mode == ‘3’:/n            e = input(‘\nEnter the public key_e >>>  ‘)/n            def enter_e():/n                global e/n                e = input(‘Enter the public key_e >>>  ‘)/n                if e == ‘‘:/n                    enter_e()/n            if e == ‘‘:/n                enter_e()/n            e = int(e)/n            def enter_n():/n                global n/n                n = input(‘Enter the public key_n >>>  ‘)/n                if n == ‘‘:/n                    enter_n()/n            enter_n()/n            n = int(n)/n            def message_enter():/n                global message/n                message = input(‘Encrypt data>>>‘)/n                if message == ‘‘:/n                    message_enter()/n            message_enter()/n            message = message.encode('unicode-escape').decode()/n            t = ' '/n            for letter in message:/n                if letter != ' ':/n                    t += CODE_DICT[letter] + ' '/n                else:/n                    t += ' '/n            result = t.replace(' ', '')/n            message = int(result)/n            # 公钥加密/n            ciphertext = Encrypt(message, e, n)/n            print(‘\n------Public Key------’)/n            print(‘N>>>‘, n)/n            print(‘\nE>>>‘, e)/n            print(‘---------END----------\n’)/n            print(‘------Encrypt data------’)/n            print(ciphertext)/n            print(‘---------END----------\n’)/n            print(‘WARN! >>> We cannot ensure the encrypt process is correct \nas the RSA_key_size may too small or the encrypt data is too large. \n’)/n            os.system('pause')/n            rsa_encrypt_process()/n        elif mode == ‘4’: /n            def rsa_encrypt_setting_mode():/n                global key_size/n                print(‘\nCHOOSE the processing mode:\n<1> <<<Back to Encryption PAGE\n<2> Setting for RSA_key_size’)/n                def enter_mode():/n                    global key_size/n                    mode = input(‘Please enter the MODE>>>  ‘)/n                    if mode == ‘1’:/n                            rsa_encrypt_process_choose_mode_2()/n                    if mode == ‘2’:/n                        def enter_new_key_size():/n                            global keysizenew/n                            global key_size/n                            keysizenew = int(input(‘\nPlease enter new RSA_key_size>>>  ‘))/n                        enter_new_key_size()/n                        if keysizenew < 10:/n                            print(‘ERROR!\nThe key size is too small!’)/n                            enter_new_key_size()/n                        elif keysizenew > 768:/n                            print(‘ERROR!\nThe key size is too large!’)/n                            enter_new_key_size()/n                        else:/n                            key_size = keysizenew/n                            print(‘SETTING DONE! keysize>>>‘, key_size, ‘bit\n’)/n                        os.system('pause')/n                        rsa_encrypt_setting_mode()/n                    else:/n                        enter_mode()/n                enter_mode()/n            rsa_encrypt_setting_mode()/n        else:/n            en_choose_mode_2()/n    en_choose_mode_2()/n/n#加密消息/ndef rsa_encrypt_data():/n    global message/n    global ciphertext/n    global plaintext/n    global result/n    global e/n    global n/n    global d/n    message = ‘‘/n    def message_enter():/n        global message/n        message = input(‘Encrypt data>>>‘)/n        if message == ‘‘:/n            message_enter()/n    message_enter()/n    #通过unicode加密/n    message = message.encode('unicode-escape').decode()/n    t = ' '/n    #通过ANSCII字典加密/n    for letter in message:/n        if letter != ' ':/n            t += CODE_DICT[letter] + ' '/n        else:/n            t += ' '/n    result = t.replace(' ', '')/n    message = int(result)/n    # 公钥加密/n    ciphertext = Encrypt(message, e, n)/n    # 私钥解密/n    plaintext = Decrypt(ciphertext, d, n)/n    rsa_output()/n/ndef rsa_encrypt_process():/n    global Encrypttimes/n    global e/n    global n/n    global d/n    global key_size/n    # 消息/n    /n    if Encrypttimes == 0:/n        rsa_encrypt_process_choose_mode_2()/n    else:/n        rsa_encrypt_process_choose_mode_1()/n/n#输出/ndef rsa_output():/n    global message/n    global ciphertext/n    global plaintext/n    global result/n    global e/n    global n/n    global d/n    global Encrypttimes/n    if message == plaintext:/n        Encrypttimes = Encrypttimes + 1/n        print(‘\nEncrypted data: Morse>>>\n’, result)/n        print(‘\nEncrypted data: RSA>>>‘)/n        print(‘Key size>>>‘, key_size, ‘bit’)/n        print(‘-------Private Key-------’)/n        print(‘N>>>‘, n)/n        print(‘\nd>>>‘, d)/n        print(‘---------END----------\n\n’)/n        print(‘------Public Key------’)/n        print(‘N>>>‘, n)/n        print(‘\nE>>>‘, e)/n        print(‘---------END----------\n’)/n        print(‘------Encrypt data------’)/n        print(ciphertext)/n        print(‘---------END----------\n’)/n        print(‘------Decrypt data------’)/n        print(‘Plaintext:  ‘, plaintext)/n        print(‘---------END----------\n’)/n        os.system('pause')/n        rsa_encrypt_process_choose_mode_1()/n/n    else:/n        def prl():/n            pr = input(‘Printed Error log？（Y/N）’)/n            if pr == ‘Y’:/n                print(‘\nEncrypted data: Morse>>>\n’, result)/n                print(‘\nEncrypted data: RSA>>>‘)/n                print(‘Key size>>>‘, key_size, ‘bit’)/n                print(‘-------Private Key-------’)/n                print(‘N>>>‘, n)/n                print(‘\nd>>>‘, d)/n                print(‘---------END----------\n\n’)/n                print(‘------Public Key------’)/n                print(‘N>>>‘, n)/n                print(‘\nE>>>‘, e)/n                print(‘---------END----------\n’)/n                print(‘------Encrypt data------’)/n                print(ciphertext)/n                print(‘---------END----------\n’)/n                print(‘------Decrypt data------’)/n                print(‘Plaintext:  ‘, plaintext)/n                print(‘---------END----------\n’)/n        print(‘\nError!\nYou entered an oversized encrypted data or a too small RSA_key_size!’)/n        prl()/n        os.system('pause')/n        rsa_encrypt_process_choose_mode_1()/n/n#客户端反馈/ndef choose_mode():/n    print(‘\nCHOOSE the processing mode:\n<1> encryption\n<2> decryption\n<3> Python code\n<4> LICENSE\n<5> EXIT’)/n    def choose_mode_1():/n        mode = input(‘Please enter the MODE>>>  ‘)/n        if mode == ‘1’:/n            rsa_encrypt_process()/n        elif mode == ‘2’:/n            rsa_decrypt_data()/n        elif mode == ‘3’:/n            print(‘\n’)/n            a = r’......’/n            lists = a.split(r’/n’)/n            for code in lists:/n                print(code)/n                time.sleep(0.1)/n            os.system('pause')/n            choose_mode()/n        elif mode == ‘4’:/n            a = r’......’/n            lists = a.split(r’\n’)/n            for code in lists:/n                print(code)/n                time.sleep(0.15)/n            os.system('pause')/n            choose_mode()/n        elif mode == ‘5’:/n            print(‘\nThank you for using RSA processor!’)/n            time.sleep(0.7)/n            print ('exiting...')/n            time.sleep(3)/n            exit ()/n        else:/n            choose_mode_1()/n    choose_mode_1()/n/nos.system('pause')/nchoose_mode()/n"
            lists = a.split(r"/n")
            for code in lists:
                print(code)
                time.sleep(0.1)
            os.system('pause')
            choose_mode()
        elif mode == "4":
            a = r"                   GNU GENERAL PUBLIC LICENSE\n                       Version 3, 29 June 2007\n\n Copyright (C) 2007 Free Software Foundation, Inc. https://fsf.org/\n Everyone is permitted to copy and distribute verbatim copies\n of this license document, but changing it is not allowed.\n\n                            Preamble\n\n  The GNU General Public License is a free, copyleft license for\nsoftware and other kinds of works.\n\n  The licenses for most software and other practical works are designed\nto take away your freedom to share and change the works.  By contrast,\nthe GNU General Public License is intended to guarantee your freedom to\nshare and change all versions of a program--to make sure it remains free\nsoftware for all its users.  We, the Free Software Foundation, use the\nGNU General Public License for most of our software; it applies also to\nany other work released this way by its authors.  You can apply it to\nyour programs, too.\n\n  When we speak of free software, we are referring to freedom, not\nprice.  Our General Public Licenses are designed to make sure that you\nhave the freedom to distribute copies of free software (and charge for\nthem if you wish), that you receive source code or can get it if you\nwant it, that you can change the software or use pieces of it in new\nfree programs, and that you know you can do these things.\n\n  To protect your rights, we need to prevent others from denying you\nthese rights or asking you to surrender the rights.  Therefore, you have\ncertain responsibilities if you distribute copies of the software, or if\nyou modify it: responsibilities to respect the freedom of others.\n\n  For example, if you distribute copies of such a program, whether\ngratis or for a fee, you must pass on to the recipients the same\nfreedoms that you received.  You must make sure that they, too, receive\nor can get the source code.  And you must show them these terms so they\nknow their rights.\n\n  Developers that use the GNU GPL protect your rights with two steps:\n(1) assert copyright on the software, and (2) offer you this License\ngiving you legal permission to copy, distribute and/or modify it.\n\n  For the developers' and authors' protection, the GPL clearly explains\nthat there is no warranty for this free software.  For both users' and\nauthors' sake, the GPL requires that modified versions be marked as\nchanged, so that their problems will not be attributed erroneously to\nauthors of previous versions.\n\n  Some devices are designed to deny users access to install or run\nmodified versions of the software inside them, although the manufacturer\ncan do so.  This is fundamentally incompatible with the aim of\nprotecting users' freedom to change the software.  The systematic\npattern of such abuse occurs in the area of products for individuals to\nuse, which is precisely where it is most unacceptable.  Therefore, we\nhave designed this version of the GPL to prohibit the practice for those\nproducts.  If such problems arise substantially in other domains, we\nstand ready to extend this provision to those domains in future versions\nof the GPL, as needed to protect the freedom of users.\n\n  Finally, every program is threatened constantly by software patents.\nStates should not allow patents to restrict development and use of\nsoftware on general-purpose computers, but in those that do, we wish to\navoid the special danger that patents applied to a free program could\nmake it effectively proprietary.  To prevent this, the GPL assures that\npatents cannot be used to render the program non-free.\n\n  The precise terms and conditions for copying, distribution and\nmodification follow.\n\n                       TERMS AND CONDITIONS\n\n  0. Definitions.\n\n  ‘This License’ refers to version 3 of the GNU General Public License.\n\n  ‘Copyright’ also means copyright-like laws that apply to other kinds of\nworks, such as semiconductor masks.\n\n  ‘The Program’ refers to any copyrightable work licensed under this\nLicense.  Each licensee is addressed as ‘you’.  ‘Licensees’ and\n’recipients’ may be individuals or organizations.\n\n  To ‘modify’ a work means to copy from or adapt all or part of the work\nin a fashion requiring copyright permission, other than the making of an\nexact copy.  The resulting work is called a ‘modified version’ of the\nearlier work or a work ‘based on’ the earlier work.\n\n  A ‘covered work’ means either the unmodified Program or a work based\non the Program.\n\n  To ‘propagate’ a work means to do anything with it that, without\npermission, would make you directly or secondarily liable for\ninfringement under applicable copyright law, except executing it on a\ncomputer or modifying a private copy.  Propagation includes copying,\ndistribution (with or without modification), making available to the\npublic, and in some countries other activities as well.\n\n  To ‘convey’ a work means any kind of propagation that enables other\nparties to make or receive copies.  Mere interaction with a user through\na computer network, with no transfer of a copy, is not conveying.\n\n  An interactive user interface displays ‘Appropriate Legal Notices’\nto the extent that it includes a convenient and prominently visible\nfeature that (1) displays an appropriate copyright notice, and (2)\ntells the user that there is no warranty for the work (except to the\nextent that warranties are provided), that licensees may convey the\nwork under this License, and how to view a copy of this License.  If\nthe interface presents a list of user commands or options, such as a\nmenu, a prominent item in the list meets this criterion.\n\n  1. Source Code.\n\n  The ‘source code’ for a work means the preferred form of the work\nfor making modifications to it.  ‘Object code’ means any non-source\nform of a work.\n\n  A ‘Standard Interface’ means an interface that either is an official\nstandard defined by a recognized standards body, or, in the case of\ninterfaces specified for a particular programming language, one that\nis widely used among developers working in that language.\n\n  The ‘System Libraries’ of an executable work include anything, other\nthan the work as a whole, that (a) is included in the normal form of\npackaging a Major Component, but which is not part of that Major\nComponent, and (b) serves only to enable use of the work with that\nMajor Component, or to implement a Standard Interface for which an\nimplementation is available to the public in source code form.  A\n’Major Component’, in this context, means a major essential component\n(kernel, window system, and so on) of the specific operating system\n(if any) on which the executable work runs, or a compiler used to\nproduce the work, or an object code interpreter used to run it.\n\n  The ‘Corresponding Source’ for a work in object code form means all\nthe source code needed to generate, install, and (for an executable\nwork) run the object code and to modify the work, including scripts to\ncontrol those activities.  However, it does not include the work's\nSystem Libraries, or general-purpose tools or generally available free\nprograms which are used unmodified in performing those activities but\nwhich are not part of the work.  For example, Corresponding Source\nincludes interface definition files associated with source files for\nthe work, and the source code for shared libraries and dynamically\nlinked subprograms that the work is specifically designed to require,\nsuch as by intimate data communication or control flow between those\nsubprograms and other parts of the work.\n\n  The Corresponding Source need not include anything that users\ncan regenerate automatically from other parts of the Corresponding\nSource.\n\n  The Corresponding Source for a work in source code form is that\nsame work.\n\n  2. Basic Permissions.\n\n  All rights granted under this License are granted for the term of\ncopyright on the Program, and are irrevocable provided the stated\nconditions are met.  This License explicitly affirms your unlimited\npermission to run the unmodified Program.  The output from running a\ncovered work is covered by this License only if the output, given its\ncontent, constitutes a covered work.  This License acknowledges your\nrights of fair use or other equivalent, as provided by copyright law.\n\n  You may make, run and propagate covered works that you do not\nconvey, without conditions so long as your license otherwise remains\nin force.  You may convey covered works to others for the sole purpose\nof having them make modifications exclusively for you, or provide you\nwith facilities for running those works, provided that you comply with\nthe terms of this License in conveying all material for which you do\nnot control copyright.  Those thus making or running the covered works\nfor you must do so exclusively on your behalf, under your direction\nand control, on terms that prohibit them from making any copies of\nyour copyrighted material outside their relationship with you.\n\n  Conveying under any other circumstances is permitted solely under\nthe conditions stated below.  Sublicensing is not allowed; section 10\nmakes it unnecessary.\n\n  3. Protecting Users' Legal Rights From Anti-Circumvention Law.\n\n  No covered work shall be deemed part of an effective technological\nmeasure under any applicable law fulfilling obligations under article\n11 of the WIPO copyright treaty adopted on 20 December 1996, or\nsimilar laws prohibiting or restricting circumvention of such\nmeasures.\n\n  When you convey a covered work, you waive any legal power to forbid\ncircumvention of technological measures to the extent such circumvention\nis effected by exercising rights under this License with respect to\nthe covered work, and you disclaim any intention to limit operation or\nmodification of the work as a means of enforcing, against the work's\nusers, your or third parties' legal rights to forbid circumvention of\ntechnological measures.\n\n  4. Conveying Verbatim Copies.\n\n  You may convey verbatim copies of the Program's source code as you\nreceive it, in any medium, provided that you conspicuously and\nappropriately publish on each copy an appropriate copyright notice;\nkeep intact all notices stating that this License and any\nnon-permissive terms added in accord with section 7 apply to the code;\nkeep intact all notices of the absence of any warranty; and give all\nrecipients a copy of this License along with the Program.\n\n  You may charge any price or no price for each copy that you convey,\nand you may offer support or warranty protection for a fee.\n\n  5. Conveying Modified Source Versions.\n\n  You may convey a work based on the Program, or the modifications to\nproduce it from the Program, in the form of source code under the\nterms of section 4, provided that you also meet all of these conditions:\n\n    a) The work must carry prominent notices stating that you modified\n    it, and giving a relevant date.\n\n    b) The work must carry prominent notices stating that it is\n    released under this License and any conditions added under section\n    7.  This requirement modifies the requirement in section 4 to\n    ‘keep intact all notices’.\n\n    c) You must license the entire work, as a whole, under this\n    License to anyone who comes into possession of a copy.  This\n    License will therefore apply, along with any applicable section 7\n    additional terms, to the whole of the work, and all its parts,\n    regardless of how they are packaged.  This License gives no\n    permission to license the work in any other way, but it does not\n    invalidate such permission if you have separately received it.\n\n    d) If the work has interactive user interfaces, each must display\n    Appropriate Legal Notices; however, if the Program has interactive\n    interfaces that do not display Appropriate Legal Notices, your\n    work need not make them do so.\n\n  A compilation of a covered work with other separate and independent\nworks, which are not by their nature extensions of the covered work,\nand which are not combined with it such as to form a larger program,\nin or on a volume of a storage or distribution medium, is called an\n’aggregate’ if the compilation and its resulting copyright are not\nused to limit the access or legal rights of the compilation's users\nbeyond what the individual works permit.  Inclusion of a covered work\nin an aggregate does not cause this License to apply to the other\nparts of the aggregate.\n\n  6. Conveying Non-Source Forms.\n\n  You may convey a covered work in object code form under the terms\nof sections 4 and 5, provided that you also convey the\nmachine-readable Corresponding Source under the terms of this License,\nin one of these ways:\n\n    a) Convey the object code in, or embodied in, a physical product\n    (including a physical distribution medium), accompanied by the\n    Corresponding Source fixed on a durable physical medium\n    customarily used for software interchange.\n\n    b) Convey the object code in, or embodied in, a physical product\n    (including a physical distribution medium), accompanied by a\n    written offer, valid for at least three years and valid for as\n    long as you offer spare parts or customer support for that product\n    model, to give anyone who possesses the object code either (1) a\n    copy of the Corresponding Source for all the software in the\n    product that is covered by this License, on a durable physical\n    medium customarily used for software interchange, for a price no\n    more than your reasonable cost of physically performing this\n    conveying of source, or (2) access to copy the\n    Corresponding Source from a network server at no charge.\n\n    c) Convey individual copies of the object code with a copy of the\n    written offer to provide the Corresponding Source.  This\n    alternative is allowed only occasionally and noncommercially, and\n    only if you received the object code with such an offer, in accord\n    with subsection 6b.\n\n    d) Convey the object code by offering access from a designated\n    place (gratis or for a charge), and offer equivalent access to the\n    Corresponding Source in the same way through the same place at no\n    further charge.  You need not require recipients to copy the\n    Corresponding Source along with the object code.  If the place to\n    copy the object code is a network server, the Corresponding Source\n    may be on a different server (operated by you or a third party)\n    that supports equivalent copying facilities, provided you maintain\n    clear directions next to the object code saying where to find the\n    Corresponding Source.  Regardless of what server hosts the\n    Corresponding Source, you remain obligated to ensure that it is\n    available for as long as needed to satisfy these requirements.\n\n    e) Convey the object code using peer-to-peer transmission, provided\n    you inform other peers where the object code and Corresponding\n    Source of the work are being offered to the general public at no\n    charge under subsection 6d.\n\n  A separable portion of the object code, whose source code is excluded\nfrom the Corresponding Source as a System Library, need not be\nincluded in conveying the object code work.\n\n  A ‘User Product’ is either (1) a ‘consumer product’, which means any\ntangible personal property which is normally used for personal, family,\nor household purposes, or (2) anything designed or sold for incorporation\ninto a dwelling.  In determining whether a product is a consumer product,\ndoubtful cases shall be resolved in favor of coverage.  For a particular\nproduct received by a particular user, ‘normally used’ refers to a\ntypical or common use of that class of product, regardless of the status\nof the particular user or of the way in which the particular user\nactually uses, or expects or is expected to use, the product.  A product\nis a consumer product regardless of whether the product has substantial\ncommercial, industrial or non-consumer uses, unless such uses represent\nthe only significant mode of use of the product.\n\n  ‘Installation Information’ for a User Product means any methods,\nprocedures, authorization keys, or other information required to install\nand execute modified versions of a covered work in that User Product from\na modified version of its Corresponding Source.  The information must\nsuffice to ensure that the continued functioning of the modified object\ncode is in no case prevented or interfered with solely because\nmodification has been made.\n\n  If you convey an object code work under this section in, or with, or\nspecifically for use in, a User Product, and the conveying occurs as\npart of a transaction in which the right of possession and use of the\nUser Product is transferred to the recipient in perpetuity or for a\nfixed term (regardless of how the transaction is characterized), the\nCorresponding Source conveyed under this section must be accompanied\nby the Installation Information.  But this requirement does not apply\nif neither you nor any third party retains the ability to install\nmodified object code on the User Product (for example, the work has\nbeen installed in ROM).\n\n  The requirement to provide Installation Information does not include a\nrequirement to continue to provide support service, warranty, or updates\nfor a work that has been modified or installed by the recipient, or for\nthe User Product in which it has been modified or installed.  Access to a\nnetwork may be denied when the modification itself materially and\nadversely affects the operation of the network or violates the rules and\nprotocols for communication across the network.\n\n  Corresponding Source conveyed, and Installation Information provided,\nin accord with this section must be in a format that is publicly\ndocumented (and with an implementation available to the public in\nsource code form), and must require no special password or key for\nunpacking, reading or copying.\n\n  7. Additional Terms.\n\n  ‘Additional permissions’ are terms that supplement the terms of this\nLicense by making exceptions from one or more of its conditions.\nAdditional permissions that are applicable to the entire Program shall\nbe treated as though they were included in this License, to the extent\nthat they are valid under applicable law.  If additional permissions\napply only to part of the Program, that part may be used separately\nunder those permissions, but the entire Program remains governed by\nthis License without regard to the additional permissions.\n\n  When you convey a copy of a covered work, you may at your option\nremove any additional permissions from that copy, or from any part of\nit.  (Additional permissions may be written to require their own\nremoval in certain cases when you modify the work.)  You may place\nadditional permissions on material, added by you to a covered work,\nfor which you have or can give appropriate copyright permission.\n\n  Notwithstanding any other provision of this License, for material you\nadd to a covered work, you may (if authorized by the copyright holders of\nthat material) supplement the terms of this License with terms:\n\n    a) Disclaiming warranty or limiting liability differently from the\n    terms of sections 15 and 16 of this License; or\n\n    b) Requiring preservation of specified reasonable legal notices or\n    author attributions in that material or in the Appropriate Legal\n    Notices displayed by works containing it; or\n\n    c) Prohibiting misrepresentation of the origin of that material, or\n    requiring that modified versions of such material be marked in\n    reasonable ways as different from the original version; or\n\n    d) Limiting the use for publicity purposes of names of licensors or\n    authors of the material; or\n\n    e) Declining to grant rights under trademark law for use of some\n    trade names, trademarks, or service marks; or\n\n    f) Requiring indemnification of licensors and authors of that\n    material by anyone who conveys the material (or modified versions of\n    it) with contractual assumptions of liability to the recipient, for\n    any liability that these contractual assumptions directly impose on\n    those licensors and authors.\n\n  All other non-permissive additional terms are considered ‘further\nrestrictions’ within the meaning of section 10.  If the Program as you\nreceived it, or any part of it, contains a notice stating that it is\ngoverned by this License along with a term that is a further\nrestriction, you may remove that term.  If a license document contains\na further restriction but permits relicensing or conveying under this\nLicense, you may add to a covered work material governed by the terms\nof that license document, provided that the further restriction does\nnot survive such relicensing or conveying.\n\n  If you add terms to a covered work in accord with this section, you\nmust place, in the relevant source files, a statement of the\nadditional terms that apply to those files, or a notice indicating\nwhere to find the applicable terms.\n\n  Additional terms, permissive or non-permissive, may be stated in the\nform of a separately written license, or stated as exceptions;\nthe above requirements apply either way.\n\n  8. Termination.\n\n  You may not propagate or modify a covered work except as expressly\nprovided under this License.  Any attempt otherwise to propagate or\nmodify it is void, and will automatically terminate your rights under\nthis License (including any patent licenses granted under the third\nparagraph of section 11).\n\n  However, if you cease all violation of this License, then your\nlicense from a particular copyright holder is reinstated (a)\nprovisionally, unless and until the copyright holder explicitly and\nfinally terminates your license, and (b) permanently, if the copyright\nholder fails to notify you of the violation by some reasonable means\nprior to 60 days after the cessation.\n\n  Moreover, your license from a particular copyright holder is\nreinstated permanently if the copyright holder notifies you of the\nviolation by some reasonable means, this is the first time you have\nreceived notice of violation of this License (for any work) from that\ncopyright holder, and you cure the violation prior to 30 days after\nyour receipt of the notice.\n\n  Termination of your rights under this section does not terminate the\nlicenses of parties who have received copies or rights from you under\nthis License.  If your rights have been terminated and not permanently\nreinstated, you do not qualify to receive new licenses for the same\nmaterial under section 10.\n\n  9. Acceptance Not Required for Having Copies.\n\n  You are not required to accept this License in order to receive or\nrun a copy of the Program.  Ancillary propagation of a covered work\noccurring solely as a consequence of using peer-to-peer transmission\nto receive a copy likewise does not require acceptance.  However,\nnothing other than this License grants you permission to propagate or\nmodify any covered work.  These actions infringe copyright if you do\nnot accept this License.  Therefore, by modifying or propagating a\ncovered work, you indicate your acceptance of this License to do so.\n\n  10. Automatic Licensing of Downstream Recipients.\n\n  Each time you convey a covered work, the recipient automatically\nreceives a license from the original licensors, to run, modify and\npropagate that work, subject to this License.  You are not responsible\nfor enforcing compliance by third parties with this License.\n\n  An ‘entity transaction’ is a transaction transferring control of an\norganization, or substantially all assets of one, or subdividing an\norganization, or merging organizations.  If propagation of a covered\nwork results from an entity transaction, each party to that\ntransaction who receives a copy of the work also receives whatever\nlicenses to the work the party's predecessor in interest had or could\ngive under the previous paragraph, plus a right to possession of the\nCorresponding Source of the work from the predecessor in interest, if\nthe predecessor has it or can get it with reasonable efforts.\n\n  You may not impose any further restrictions on the exercise of the\nrights granted or affirmed under this License.  For example, you may\nnot impose a license fee, royalty, or other charge for exercise of\nrights granted under this License, and you may not initiate litigation\n(including a cross-claim or counterclaim in a lawsuit) alleging that\nany patent claim is infringed by making, using, selling, offering for\nsale, or importing the Program or any portion of it.\n\n  11. Patents.\n\n  A ‘contributor’ is a copyright holder who authorizes use under this\nLicense of the Program or a work on which the Program is based.  The\nwork thus licensed is called the contributor's ‘contributor version’.\n\n  A contributor's ‘essential patent claims’ are all patent claims\nowned or controlled by the contributor, whether already acquired or\nhereafter acquired, that would be infringed by some manner, permitted\nby this License, of making, using, or selling its contributor version,\nbut do not include claims that would be infringed only as a\nconsequence of further modification of the contributor version.  For\npurposes of this definition, ‘control’ includes the right to grant\npatent sublicenses in a manner consistent with the requirements of\nthis License.\n\n  Each contributor grants you a non-exclusive, worldwide, royalty-free\npatent license under the contributor's essential patent claims, to\nmake, use, sell, offer for sale, import and otherwise run, modify and\npropagate the contents of its contributor version.\n\n  In the following three paragraphs, a ‘patent license’ is any express\nagreement or commitment, however denominated, not to enforce a patent\n(such as an express permission to practice a patent or covenant not to\nsue for patent infringement).  To ‘grant’ such a patent license to a\nparty means to make such an agreement or commitment not to enforce a\npatent against the party.\n\n  If you convey a covered work, knowingly relying on a patent license,\nand the Corresponding Source of the work is not available for anyone\nto copy, free of charge and under the terms of this License, through a\npublicly available network server or other readily accessible means,\nthen you must either (1) cause the Corresponding Source to be so\navailable, or (2) arrange to deprive yourself of the benefit of the\npatent license for this particular work, or (3) arrange, in a manner\nconsistent with the requirements of this License, to extend the patent\nlicense to downstream recipients.  ‘Knowingly relying’ means you have\nactual knowledge that, but for the patent license, your conveying the\ncovered work in a country, or your recipient's use of the covered work\nin a country, would infringe one or more identifiable patents in that\ncountry that you have reason to believe are valid.\n\n  If, pursuant to or in connection with a single transaction or\narrangement, you convey, or propagate by procuring conveyance of, a\ncovered work, and grant a patent license to some of the parties\nreceiving the covered work authorizing them to use, propagate, modify\nor convey a specific copy of the covered work, then the patent license\nyou grant is automatically extended to all recipients of the covered\nwork and works based on it.\n\n  A patent license is ‘discriminatory’ if it does not include within\nthe scope of its coverage, prohibits the exercise of, or is\nconditioned on the non-exercise of one or more of the rights that are\nspecifically granted under this License.  You may not convey a covered\nwork if you are a party to an arrangement with a third party that is\nin the business of distributing software, under which you make payment\nto the third party based on the extent of your activity of conveying\nthe work, and under which the third party grants, to any of the\nparties who would receive the covered work from you, a discriminatory\npatent license (a) in connection with copies of the covered work\nconveyed by you (or copies made from those copies), or (b) primarily\nfor and in connection with specific products or compilations that\ncontain the covered work, unless you entered into that arrangement,\nor that patent license was granted, prior to 28 March 2007.\n\n  Nothing in this License shall be construed as excluding or limiting\nany implied license or other defenses to infringement that may\notherwise be available to you under applicable patent law.\n\n  12. No Surrender of Others' Freedom.\n\n  If conditions are imposed on you (whether by court order, agreement or\notherwise) that contradict the conditions of this License, they do not\nexcuse you from the conditions of this License.  If you cannot convey a\ncovered work so as to satisfy simultaneously your obligations under this\nLicense and any other pertinent obligations, then as a consequence you may\nnot convey it at all.  For example, if you agree to terms that obligate you\nto collect a royalty for further conveying from those to whom you convey\nthe Program, the only way you could satisfy both those terms and this\nLicense would be to refrain entirely from conveying the Program.\n\n  13. Use with the GNU Affero General Public License.\n\n  Notwithstanding any other provision of this License, you have\npermission to link or combine any covered work with a work licensed\nunder version 3 of the GNU Affero General Public License into a single\ncombined work, and to convey the resulting work.  The terms of this\nLicense will continue to apply to the part which is the covered work,\nbut the special requirements of the GNU Affero General Public License,\nsection 13, concerning interaction through a network will apply to the\ncombination as such.\n\n  14. Revised Versions of this License.\n\n  The Free Software Foundation may publish revised and/or new versions of\nthe GNU General Public License from time to time.  Such new versions will\nbe similar in spirit to the present version, but may differ in detail to\naddress new problems or concerns.\n\n  Each version is given a distinguishing version number.  If the\nProgram specifies that a certain numbered version of the GNU General\nPublic License ‘or any later version’ applies to it, you have the\noption of following the terms and conditions either of that numbered\nversion or of any later version published by the Free Software\nFoundation.  If the Program does not specify a version number of the\nGNU General Public License, you may choose any version ever published\nby the Free Software Foundation.\n\n  If the Program specifies that a proxy can decide which future\nversions of the GNU General Public License can be used, that proxy's\npublic statement of acceptance of a version permanently authorizes you\nto choose that version for the Program.\n\n  Later license versions may give you additional or different\npermissions.  However, no additional obligations are imposed on any\nauthor or copyright holder as a result of your choosing to follow a\nlater version.\n\n  15. Disclaimer of Warranty.\n\n  THERE IS NO WARRANTY FOR THE PROGRAM, TO THE EXTENT PERMITTED BY\nAPPLICABLE LAW.  EXCEPT WHEN OTHERWISE STATED IN WRITING THE COPYRIGHT\nHOLDERS AND/OR OTHER PARTIES PROVIDE THE PROGRAM ‘AS IS’ WITHOUT WARRANTY\nOF ANY KIND, EITHER EXPRESSED OR IMPLIED, INCLUDING, BUT NOT LIMITED TO,\nTHE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR\nPURPOSE.  THE ENTIRE RISK AS TO THE QUALITY AND PERFORMANCE OF THE PROGRAM\nIS WITH YOU.  SHOULD THE PROGRAM PROVE DEFECTIVE, YOU ASSUME THE COST OF\nALL NECESSARY SERVICING, REPAIR OR CORRECTION.\n\n  16. Limitation of Liability.\n\n  IN NO EVENT UNLESS REQUIRED BY APPLICABLE LAW OR AGREED TO IN WRITING\nWILL ANY COPYRIGHT HOLDER, OR ANY OTHER PARTY WHO MODIFIES AND/OR CONVEYS\nTHE PROGRAM AS PERMITTED ABOVE, BE LIABLE TO YOU FOR DAMAGES, INCLUDING ANY\nGENERAL, SPECIAL, INCIDENTAL OR CONSEQUENTIAL DAMAGES ARISING OUT OF THE\nUSE OR INABILITY TO USE THE PROGRAM (INCLUDING BUT NOT LIMITED TO LOSS OF\nDATA OR DATA BEING RENDERED INACCURATE OR LOSSES SUSTAINED BY YOU OR THIRD\nPARTIES OR A FAILURE OF THE PROGRAM TO OPERATE WITH ANY OTHER PROGRAMS),\nEVEN IF SUCH HOLDER OR OTHER PARTY HAS BEEN ADVISED OF THE POSSIBILITY OF\nSUCH DAMAGES.\n\n  17. Interpretation of Sections 15 and 16.\n\n  If the disclaimer of warranty and limitation of liability provided\nabove cannot be given local legal effect according to their terms,\nreviewing courts shall apply local law that most closely approximates\nan absolute waiver of all civil liability in connection with the\nProgram, unless a warranty or assumption of liability accompanies a\ncopy of the Program in return for a fee.\n\n                     END OF TERMS AND CONDITIONS\n\n            How to Apply These Terms to Your New Programs\n\n  If you develop a new program, and you want it to be of the greatest\npossible use to the public, the best way to achieve this is to make it\nfree software which everyone can redistribute and change under these terms.\n\n  To do so, attach the following notices to the program.  It is safest\nto attach them to the start of each source file to most effectively\nstate the exclusion of warranty; and each file should have at least\nthe ‘copyright’ line and a pointer to where the full notice is found.\n\n    one line to give the program's name and a brief idea of what it does.\n    Copyright (C) year  name of author\n\n    This program is free software: you can redistribute it and/or modify\n    it under the terms of the GNU General Public License as published by\n    the Free Software Foundation, either version 3 of the License, or\n    (at your option) any later version.\n\n    This program is distributed in the hope that it will be useful,\n    but WITHOUT ANY WARRANTY; without even the implied warranty of\n    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the\n    GNU General Public License for more details.\n\n    You should have received a copy of the GNU General Public License\n    along with this program.  If not, see https://www.gnu.org/licenses/.\n\nAlso add information on how to contact you by electronic and paper mail.\n\n  If the program does terminal interaction, make it output a short\nnotice like this when it starts in an interactive mode:\n\n    program  Copyright (C) year  name of author\n    This program comes with ABSOLUTELY NO WARRANTY; for details type `show w'.\n    This is free software, and you are welcome to redistribute it\n    under certain conditions; type `show c' for details.\n\nThe hypothetical commands `show w' and `show c' should show the appropriate\nparts of the General Public License.  Of course, your program's commands\nmight be different; for a GUI interface, you would use an ‘about box’.\n\n  You should also get your employer (if you work as a programmer) or school,\nif any, to sign a ‘copyright disclaimer’ for the program, if necessary.\nFor more information on this, and how to apply and follow the GNU GPL, see\nhttps://www.gnu.org/licenses/.\n\n  The GNU General Public License does not permit incorporating your program\ninto proprietary programs.  If your program is a subroutine library, you\nmay consider it more useful to permit linking proprietary applications with\nthe library.  If this is what you want to do, use the GNU Lesser General\nPublic License instead of this License.  But first, please read\nhttps://www.gnu.org/licenses/why-not-lgpl.html.\n"
            lists = a.split(r"\n")
            for code in lists:
                print(code)
                time.sleep(0.1)
            os.system('pause')
            choose_mode()
        elif mode == "5":
            print("\nThank you for using RSA processor!")
            time.sleep(0.7)
            print ('exiting...')
            time.sleep(3)
            exit ()
        else:
            choose_mode_1()
    choose_mode_1()

os.system('pause')
choose_mode()
