package com.example.backend.presentation.controllers;

import org.springframework.beans.factory.annotation.Autowired;
import org.springframework.web.bind.annotation.GetMapping;
import org.springframework.web.bind.annotation.PostMapping;
import org.springframework.web.bind.annotation.RequestMapping;
import org.springframework.web.bind.annotation.RestController;

import com.example.backend.business.entities.CreateUserDTO;
import com.example.backend.business.service.interfaces.IUserService;
import com.example.backend.core.enums.Role;
import com.example.backend.core.exceptions.ExistingAccountException;
import com.example.backend.presentation.entities.request.CreateUserRequest;
import com.example.backend.presentation.entities.response.AuthResponse;
import com.example.backend.presentation.entities.response.BaseResponse;
import com.example.backend.presentation.entities.response.ErrorResponse;

import io.swagger.v3.oas.annotations.parameters.RequestBody;

@RestController()
@RequestMapping("/user")
public class UserController {

    @Autowired
    private IUserService userService;

    @GetMapping("/status")
    public String status() {
        return "User service is running.";
    }

    @PostMapping("/login")
    public BaseResponse<AuthResponse> login(@RequestBody CreateUserRequest request) {
        var isValid = userService.validateUserCredentials(request.getUsername(), request.getPassword());

        if (isValid) {
            var user = userService.getUserByEmail(request.getUsername());
            var token = userService.generateAuthToken(user.getUsername(), user.getId());
            var authResponse = new AuthResponse(true, token);
            return new BaseResponse<>(authResponse, 200);
        } else {
            return new ErrorResponse<AuthResponse, CreateUserRequest>(request, "Invalid credentials", 401);
        }
    }

    @PostMapping("/register")
    public BaseResponse<AuthResponse> register(@RequestBody CreateUserRequest request) {
        try {
            var createUserDto = new CreateUserDTO(request.getUsername(), request.getPassword(), Role.STUDENT);
            var user = userService.createUser(createUserDto);
            var token = userService.generateAuthToken(user.getUsername(), user.getId());
            var authResponse = new AuthResponse(true, token);
            return new BaseResponse<>(authResponse, 201);
        } catch (ExistingAccountException e) {
            return new ErrorResponse<AuthResponse, CreateUserRequest>(request, e.getMessage(), 409);
        } catch (Exception e) {
            return new ErrorResponse<AuthResponse, CreateUserRequest>(request, "Internal server error", 500);
        }
    }
}
