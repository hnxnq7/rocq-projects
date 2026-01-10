biliFollowing = {}

print("请输入总共关注的up主人数：")
totalFollowing = int(input())
for i in range(totalFollowing):
    print("请输入第", i+1, "位up主名称：")
    follow = input()
    print("请输入第", i+1, "位up主分区：")
    section = input()
    if section in biliFollowing:
        biliFollowing[section].append(follow)
    else:
        biliFollowing[section] = [follow]

for key in biliFollowing.keys():
# for key in biliFollowing: (???)
    print("\n", key, ":", end = " ")
    for i in biliFollowing[key]:
        print(i, "\n\t", end = "")
    print("共", len(biliFollowing[key]), "人")